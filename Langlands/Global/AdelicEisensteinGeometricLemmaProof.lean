import Langlands.Global.AdelicEisensteinGeometricLemmaStatement
import Langlands.Global.AdelicEisensteinDoubleCosetsProof
import Langlands.GroupScheme.Rational.StandardWeylMinimalRepresentativesProof
import Langlands.GroupScheme.Rational.DynamicNestedParabolicDecompositionReduction
import Langlands.GroupScheme.Rational.DynamicNestedParabolicDecompositionProof
import Langlands.GroupScheme.RepresentedSubgroupTransport

/-! # Standard parabolics in the adelic geometric lemma -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints Langlands.GroupScheme.GaloisPointComparison
  Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

section Rational

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
  [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)

include hG hi hν

omit [Mono i.hom.hom.left] in
private theorem standardParabolic_le_of_subset
    {P₁ P : Finset (SimpleRoot i ν)} (h : P₁ ⊆ P) :
    standardParabolic i ν (rootSet i ν P₁) ≤ standardParabolic i ν (rootSet i ν P) :=
  ((standardParabolicOrder F G hG T i hi ν hν).1 _ _
    (rootSet_subset i ν P₁) (rootSet_subset i ν P)).1.mp
    ((rootSet_subset_iff i ν P₁ P).mpr h)

omit [Mono i.hom.hom.left] in
private theorem standardParabolic_eq_inf_sup
    (P Q P₁ : Finset (SimpleRoot i ν)) (n : normalizerPoints i) (hP₁ : P₁ ⊆ P)
    (hL : levi i ν P ⊓ (parabolic i ν Q).map (MulAut.conj n.val).toMonoidHom =
      levi i ν P ⊓ parabolic i ν P₁) :
    parabolic i ν P₁ =
      (parabolic i ν P ⊓ (parabolic i ν Q).map (MulAut.conj n.val).toMonoidHom) ⊔
        unipotent i ν P := by
  have := hG.isSeparated
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let Qn := (parabolic i ν Q).map (MulAut.conj n.val).toMonoidHom
  let H := parabolic i ν P ⊓ Qn
  let U := unipotent i ν P
  have hNested := nestedLeviDecomposition_standard_of_dynamic
    dynamicNestedParabolicDecomposition standardCocharacter standardParabolicOrder
    F G hG T i hi ν hν (rootSet i ν P₁) (rootSet i ν P)
    (rootSet_subset i ν P₁) (rootSet_subset i ν P) ((rootSet_subset_iff i ν P₁ P).mpr hP₁)
  have hSmall : (parabolic i ν P₁ : Set (rationalPoints G)) =
      ((levi i ν P ⊓ parabolic i ν P₁ : Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
        (unipotent i ν P : Set (rationalPoints G)) :=
    hNested.identityTest_products.2.2
  have hBig :
      ((Qn ⊓ parabolic i ν P : Subgroup (rationalPoints G)) : Set (rationalPoints G)) =
        ((Qn ⊓ levi i ν P : Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
          ((Qn ⊓ unipotent i ν P : Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
    obtain ⟨eta, hQ, -, -⟩ := StandardWeylMinimal.exists_map_conj_eq_dynamic i ν hG hi hν Q n
    obtain ⟨mu, hP, hM, hU⟩ := StandardWeylMinimal.exists_eq_dynamic i ν hG hi hν P
    dsimp only [Qn]
    rw [hQ, hP, hM, hU]
    exact Dynamic.parabolic_inf_parabolic_eq_mul i (CommGroupScheme.groupHom eta)
      (CommGroupScheme.groupHom mu) (Over.mk (𝟙 _))
  apply le_antisymm
  · intro x hx
    change x ∈ (parabolic i ν P₁ : Set (rationalPoints G)) at hx
    rw [hSmall, ← hL] at hx
    obtain ⟨m, hm, u, hu, rfl⟩ := Set.mem_mul.mp hx
    have hm' : m ∈ H := ⟨levi_le_parabolic i ν P hm.1, hm.2⟩
    exact (H ⊔ U).mul_mem ((show H ≤ H ⊔ U from le_sup_left) hm')
      ((show U ≤ H ⊔ U from le_sup_right) hu)
  · refine sup_le ?_ ?_
    · intro x hx
      have hx' : x ∈ (↑(Qn ⊓ parabolic i ν P) : Set (rationalPoints G)) := ⟨hx.2, hx.1⟩
      rw [hBig] at hx'
      obtain ⟨m, hm, u, hu, rfl⟩ := Set.mem_mul.mp hx'
      change m * u ∈ (parabolic i ν P₁ : Set (rationalPoints G))
      rw [hSmall, ← hL]
      exact Set.mem_mul.mpr ⟨m, ⟨hm.2, hm.1⟩, u, hu.2, rfl⟩
    · intro u hu
      change u ∈ (parabolic i ν P₁ : Set (rationalPoints G))
      rw [hSmall]
      exact Set.mem_mul.mpr ⟨1, one_mem _, u, hu, one_mul _⟩

end Rational

section Adelic

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

private theorem principalPoint_map_conj (H : Subgroup (rationalPoints G)) (x : rationalPoints G) :
    (H.map (MulAut.conj x).toMonoidHom).map (principalPoint F G) =
      (H.map (principalPoint F G)).map
        (MulAut.conj (principalPoint F G x)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro y
  change principalPoint F G (x * y * x⁻¹) =
    principalPoint F G x * principalPoint F G y * (principalPoint F G x)⁻¹
  rw [map_mul, map_mul, map_inv]

variable [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

private theorem rationalImage_standardParabolic (P : Finset (SimpleRoot i ν)) :
    rationalImage F (Standard.parabolicHom i ν (rootSet i ν P)) =
      (parabolic i ν P).map (principalPoint F G) := by
  rw [rationalImage_eq_map_range, (Standard.isRepresentedBy_parabolicHom i ν _).2]

private theorem rationalImage_standardUnipotent (P : Finset (SimpleRoot i ν)) :
    rationalImage F (Standard.unipotentToParabolic i ν (rootSet i ν P) ≫
      Standard.parabolicHom i ν (rootSet i ν P)) =
      (unipotent i ν P).map (principalPoint F G) := by
  rw [Standard.unipotentToParabolic_comp, rationalImage_eq_map_range,
    (Standard.isRepresentedBy_unipotentHom i ν _).2]

end Adelic

private theorem comap_inf_inner {S : Scheme.{u}} {G : GroupScheme S}
    (e : G ≅ G) (A B : SubgroupFunctor G) :
    (A.comap e.hom ⊓ B).comap e.inv = A ⊓ B.comap e.inv := by
  rw [SubgroupFunctor.comap_inf, ← SubgroupFunctor.comap_comp, e.inv_hom_id,
    SubgroupFunctor.comap_id]

private theorem inf_eq_of_intersection_product {H : Type*} [Group H]
    (U P M N R : Subgroup H)
    (hprod : (↑(U ⊓ P) : Set H) = (↑(U ⊓ M) : Set H) * (↑(U ⊓ N) : Set H))
    (hM : M ⊓ U ≤ R) (hN : N ≤ R) (hR : R ≤ P) :
    U ⊓ P = U ⊓ R := by
  apply le_antisymm
  · intro x hx
    change x ∈ (↑(U ⊓ P) : Set H) at hx
    rw [hprod] at hx
    obtain ⟨m, hm, v, hv, rfl⟩ := Set.mem_mul.mp hx
    exact ⟨U.mul_mem hm.1 hv.1, R.mul_mem (hM ⟨hm.2, hm.1⟩) (hN hv.2)⟩
  · intro x hx
    exact ⟨hx.1, hR hx.2⟩

section Radical

variable
    (F : Type u) [Field F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    {CM : CoxeterMatrix (SimpleRoot i ν)} (cs : CoxeterSystem CM (relativeWeylGroup i))
    (hcs : letI := hi.isSplitSubtorus.mono; IsRelativeWeylCoxeterRealization i ν cs)
    (P Q : Finset (SimpleRoot i ν)) (n : normalizerPoints i)
    (hmin : IsMinimal cs Q P (QuotientGroup.mk n))

include hG hi hν in
private theorem standardUnipotent_comap_intersection_product
    (X : Over (Spec (CommRingCat.of F))) :
    let U := (standardUnipotent i ν (rootSet i ν Q)).comap (G.innerIso n.val).hom
    let PP := standardParabolic i ν (rootSet i ν P)
    let LP := standardLevi i ν (rootSet i ν P)
    let UP := standardUnipotent i ν (rootSet i ν P)
    ((U ⊓ PP).carrier X : Set (X ⟶ G.X)) =
      ((U ⊓ LP).carrier X : Set (X ⟶ G.X)) * ((U ⊓ UP).carrier X : Set (X ⟶ G.X)) := by
  have := hG.isSeparated
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨⟨zeta, hzeta⟩, hQ⟩ := standardCocharacter F G hG T i hi ν hν
    (rootSet i ν Q) (rootSet_subset i ν Q)
  obtain ⟨⟨eta, heta⟩, hP⟩ := standardCocharacter F G hG T i hi ν hν
    (rootSet i ν P) (rootSet_subset i ν P)
  obtain ⟨hPa, hLe, hUn⟩ := hP eta heta
  dsimp only
  rw [(hQ zeta hzeta).2.2, hPa, hLe, hUn, dynamicUnipotent_comap_innerIso]
  exact Dynamic.unipotent_inf_parabolic_eq_mul i _ _ X

include hG hi hν hcs hmin

/-- In Bernstein–Lapid Lemma 6.7(iii), intersecting the target radical with the
Weyl conjugate of the source parabolic gives the same subgroup functor as
intersecting it with the conjugate of the smaller source radical. -/
theorem standardGeometricLemmaRadicalIntersection :
    let P₁ := intersectionSubset cs Q P (QuotientGroup.mk n)
    let e := G.innerIso n.val
    let UQ := standardUnipotent i ν (rootSet i ν Q)
    UQ ⊓ (standardParabolic i ν (rootSet i ν P)).comap e.inv =
      UQ ⊓ (standardUnipotent i ν (rootSet i ν P₁)).comap e.inv := by
  let P₁ := intersectionSubset cs Q P (QuotientGroup.mk n)
  let e := G.innerIso n.val
  let UQ := standardUnipotent i ν (rootSet i ν Q)
  let UP₁ := standardUnipotent i ν (rootSet i ν P₁)
  let LP := standardLevi i ν (rootSet i ν P)
  let PP := standardParabolic i ν (rootSet i ν P)
  let UP := standardUnipotent i ν (rootSet i ν P)
  let U := UQ.comap e.hom
  have hP₁ : P₁ ⊆ P := intersectionSubset_subset cs Q P _
  have hJP : rootSet i ν P₁ ⊆ rootSet i ν P := (rootSet_subset_iff i ν P₁ P).mpr hP₁
  have hOrder := (standardParabolicOrder F G hG T i hi ν hν).1
  have hUP : UP ≤ UP₁ :=
    ((hOrder _ _ (rootSet_subset i ν P₁) (rootSet_subset i ν P)).2 hJP).2
  have hUP₁ : UP₁ ≤ PP :=
    (standardUnipotent_le_standardParabolic i ν (rootSet i ν P₁)).trans
      (standardParabolic_le_of_subset i ν hG hi hν hP₁)
  have hSource := standardSourceTwistedIntersection F G hG T i hi ν hν CM cs hcs
  have hSourceRad : LP ⊓ U = LP ⊓ UP₁ := (hSource Q P _ hmin n rfl).2
  have hInner : U ⊓ PP = U ⊓ UP₁ := by
    apply SubgroupFunctor.ext
    intro X
    have hL : (LP ⊓ U).carrier X ≤ UP₁.carrier X := by
      rw [hSourceRad]
      exact inf_le_right
    exact inf_eq_of_intersection_product (U.carrier X) (PP.carrier X)
      (LP.carrier X) (UP.carrier X) (UP₁.carrier X)
      (standardUnipotent_comap_intersection_product F G hG T i hi ν hν P Q n X)
      hL (hUP X) (hUP₁ X)
  exact (comap_inf_inner e UQ PP).symm.trans <|
    (congrArg (SubgroupFunctor.comap e.inv) hInner).trans (comap_inf_inner e UQ UP₁)

/-- The target radical of the smaller geometric-lemma parabolic factors on
every test scheme as in Bernstein–Lapid Lemma 6.7(iii). -/
theorem standardGeometricLemmaRadicalProduct (X : Over (Spec (CommRingCat.of F))) :
    let P₁ := intersectionSubset cs Q P (QuotientGroup.mk n)
    let Q₁ := intersectionSubset cs P Q (QuotientGroup.mk n)⁻¹
    let e := G.innerIso n.val
    let UQ := standardUnipotent i ν (rootSet i ν Q)
    let UP₁ := standardUnipotent i ν (rootSet i ν P₁)
    let UQ₁ := standardUnipotent i ν (rootSet i ν Q₁)
    (UQ₁.carrier X : Set (X ⟶ G.X)) =
      ((UQ₁ ⊓ UP₁.comap e.inv).carrier X : Set (X ⟶ G.X)) *
        (UQ.carrier X : Set (X ⟶ G.X)) := by
  let P₁ := intersectionSubset cs Q P (QuotientGroup.mk n)
  let Q₁ := intersectionSubset cs P Q (QuotientGroup.mk n)⁻¹
  let e := G.innerIso n.val
  let UQ := standardUnipotent i ν (rootSet i ν Q)
  let UP₁ := standardUnipotent i ν (rootSet i ν P₁)
  let UQ₁ := standardUnipotent i ν (rootSet i ν Q₁)
  let LQ := standardLevi i ν (rootSet i ν Q)
  let UP := standardUnipotent i ν (rootSet i ν P)
  have hP₁ : P₁ ⊆ P := intersectionSubset_subset cs Q P _
  have hQ₁ : Q₁ ⊆ Q := intersectionSubset_subset cs P Q _
  have hJP : rootSet i ν P₁ ⊆ rootSet i ν P := (rootSet_subset_iff i ν P₁ P).mpr hP₁
  have hJQ : rootSet i ν Q₁ ⊆ rootSet i ν Q := (rootSet_subset_iff i ν Q₁ Q).mpr hQ₁
  have hOrder := (standardParabolicOrder F G hG T i hi ν hν).1
  have hUP : UP ≤ UP₁ :=
    ((hOrder _ _ (rootSet_subset i ν P₁) (rootSet_subset i ν P)).2 hJP).2
  have hUQ : UQ ≤ UQ₁ :=
    ((hOrder _ _ (rootSet_subset i ν Q₁) (rootSet_subset i ν Q)).2 hJQ).2
  have hSource := standardSourceTwistedIntersection F G hG T i hi ν hν CM cs hcs
  have hInv : IsMinimal cs P Q (QuotientGroup.mk n)⁻¹ := isMinimal_inv cs hmin
  have hTargetRad := (hSource P Q _ hInv n⁻¹ rfl).2
  rw [Subgroup.coe_inv, G.innerIso_inv_hom] at hTargetRad
  change LQ ⊓ UP.comap e.inv = LQ ⊓ UQ₁ at hTargetRad
  have hNested := nestedLeviDecomposition_standard_of_dynamic
    dynamicNestedParabolicDecomposition standardCocharacter standardParabolicOrder
    F G hG T i hi ν hν (rootSet i ν Q₁) (rootSet i ν Q)
    (rootSet_subset i ν Q₁) (rootSet_subset i ν Q) hJQ
  have hProd : (UQ₁.carrier X : Set (X ⟶ G.X)) =
      ((LQ ⊓ UQ₁).carrier X : Set (X ⟶ G.X)) * (UQ.carrier X : Set (X ⟶ G.X)) :=
    (hNested X).2.2.2.2.2.1
  apply Set.Subset.antisymm
  · intro x hx
    rw [hProd, ← hTargetRad] at hx
    obtain ⟨m, hm, v, hv, rfl⟩ := Set.mem_mul.mp hx
    have hm' : m ∈ (LQ ⊓ UP.comap e.inv).carrier X := hm
    rw [hTargetRad] at hm'
    exact Set.mem_mul.mpr
      ⟨m, ⟨hm'.2, (SubgroupFunctor.comap_mono hUP) X hm.2⟩, v, hv, rfl⟩
  · rintro x ⟨m, hm, v, hv, rfl⟩
    exact (UQ₁.carrier X).mul_mem hm.1 (hUQ X hv)

end Radical

/-- For minimum-length representatives the two smaller parabolics have the
canonical Coxeter intersection indices. The rational representative also
conjugates their represented standard Levis. -/
theorem eisensteinGeometricLemmaDatum_of_minimal
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    {CM : CoxeterMatrix (SimpleRoot i ν)} (cs : CoxeterSystem CM (relativeWeylGroup i))
    (hcs : IsRelativeWeylCoxeterRealization i ν cs)
    (P Q : Finset (SimpleRoot i ν)) (n : normalizerPoints i)
    (hmin : IsMinimal cs Q P (QuotientGroup.mk n)) :
    let P₁ := intersectionSubset cs Q P (QuotientGroup.mk n)
    let Q₁ := intersectionSubset cs P Q (QuotientGroup.mk n)⁻¹
    ∃ (f : Standard.parabolicScheme i ν (rootSet i ν P₁) ⟶
        Standard.parabolicScheme i ν (rootSet i ν P))
      (g' : Standard.parabolicScheme i ν (rootSet i ν Q₁) ⟶
        Standard.parabolicScheme i ν (rootSet i ν Q)),
      f ≫ Standard.parabolicHom i ν (rootSet i ν P) =
        Standard.parabolicHom i ν (rootSet i ν P₁) ∧
      g' ≫ Standard.parabolicHom i ν (rootSet i ν Q) =
        Standard.parabolicHom i ν (rootSet i ν Q₁) ∧
      IsGeometricLemmaDatum
        (Standard.parabolicHom i ν (rootSet i ν P))
        (Standard.unipotentToParabolic i ν (rootSet i ν P))
        (Standard.parabolicHom i ν (rootSet i ν Q))
        (Standard.unipotentToParabolic i ν (rootSet i ν Q)) f g' n.val ∧
      (∀ K : Subgroup (AdelicGroupPoints F G),
        IsIwasawaCompact (Standard.parabolicHom i ν ∅) K →
          IsIwasawaCompact (f ≫ Standard.parabolicHom i ν (rootSet i ν P)) K ∧
          IsIwasawaCompact (g' ≫ Standard.parabolicHom i ν (rootSet i ν Q)) K) ∧
      ∃ c : Standard.leviScheme i ν (rootSet i ν Q₁) ⟶
          Standard.leviScheme i ν (rootSet i ν P₁),
        IsWeylConjugation (Standard.parabolicHom i ν (rootSet i ν P₁))
          (Standard.leviToParabolic i ν (rootSet i ν P₁))
          (Standard.parabolicHom i ν (rootSet i ν Q₁))
          (Standard.leviToParabolic i ν (rootSet i ν Q₁)) n.val c := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let P₁ := intersectionSubset cs Q P (QuotientGroup.mk n)
  let Q₁ := intersectionSubset cs P Q (QuotientGroup.mk n)⁻¹
  let w : relativeWeylGroup i := QuotientGroup.mk n
  have hP₁ : P₁ ⊆ P := intersectionSubset_subset cs Q P w
  have hQ₁ : Q₁ ⊆ Q := intersectionSubset_subset cs P Q w⁻¹
  have hminInv := isMinimal_inv cs hmin
  have hSource := standardSourceTwistedIntersection F G hG T i hi ν hν CM cs hcs
  obtain ⟨hPL, -⟩ := standardSourcePoints_twistedIntersection_of_functor_eq i ν Q P P₁
    n.val (hSource Q P w hmin n rfl).1 (hSource Q P w hmin n rfl).2
  obtain ⟨hQL, -⟩ := standardSourcePoints_twistedIntersection_of_functor_eq i ν P Q Q₁
    (n⁻¹ : normalizerPoints i).val
    (hSource P Q w⁻¹ hminInv n⁻¹ rfl).1 (hSource P Q w⁻¹ hminInv n⁻¹ rfl).2
  rw [Subgroup.coe_inv, inv_inv] at hQL
  have hPL' : levi i ν P ⊓ (parabolic i ν Q).map
      (MulAut.conj (n⁻¹ : normalizerPoints i).val).toMonoidHom = levi i ν P ⊓ parabolic i ν P₁ := by
    rw [Subgroup.coe_inv]
    exact hPL
  let f := (Standard.isRepresentedBy_parabolicHom i ν (rootSet i ν P₁)).inclusionHom
    (Standard.isRepresentedBy_parabolicHom i ν (rootSet i ν P))
    (standardParabolic_le_of_subset i ν hG hi hν hP₁)
  let g' := (Standard.isRepresentedBy_parabolicHom i ν (rootSet i ν Q₁)).inclusionHom
    (Standard.isRepresentedBy_parabolicHom i ν (rootSet i ν Q))
    (standardParabolic_le_of_subset i ν hG hi hν hQ₁)
  have hf : f ≫ Standard.parabolicHom i ν (rootSet i ν P) =
      Standard.parabolicHom i ν (rootSet i ν P₁) :=
    SubgroupFunctor.IsRepresentedBy.inclusionHom_comp _ _ _
  have hg' : g' ≫ Standard.parabolicHom i ν (rootSet i ν Q) =
      Standard.parabolicHom i ν (rootSet i ν Q₁) :=
    SubgroupFunctor.IsRepresentedBy.inclusionHom_comp _ _ _
  refine ⟨f, g', hf, hg', ?_, ?_, ?_⟩
  · have hinj : Function.Injective (principalPoint F G) :=
      (rational_injective F G).comp (rationalCoeffEquiv F G).injective
    have hPmap := congrArg (Subgroup.map (principalPoint F G))
      (standardParabolic_eq_inf_sup i ν hG hi hν P Q P₁ n⁻¹ hP₁ hPL')
    have hQmap := congrArg (Subgroup.map (principalPoint F G))
      (standardParabolic_eq_inf_sup i ν hG hi hν Q P Q₁ n hQ₁ hQL)
    simp only [Subgroup.map_sup, Subgroup.map_inf _ _ _ hinj,
      principalPoint_map_conj] at hPmap hQmap
    rw [Subgroup.coe_inv, map_inv] at hPmap
    rw [principalPoint_eq_innerAdelicPoint] at hPmap hQmap
    constructor
    · rw [hf, rationalImage_standardParabolic F G, rationalImage_standardParabolic F G,
        rationalImage_standardParabolic F G, rationalImage_standardUnipotent F G]
      exact hPmap
    · rw [hg', rationalImage_standardParabolic F G, rationalImage_standardParabolic F G,
        rationalImage_standardParabolic F G, rationalImage_standardUnipotent F G]
      exact hQmap
  · intro K hK
    have hStd (J : Finset (SimpleRoot i ν)) :
        IsIwasawaCompact (Standard.parabolicHom i ν (rootSet i ν J)) K := by
      have hOrder : standardParabolic i ν ∅ ≤ standardParabolic i ν (rootSet i ν J) :=
        ((standardParabolicOrder F G hG T i hi ν hν).1 ∅ _ (Set.empty_subset _)
          (rootSet_subset i ν J)).1.mp (Set.empty_subset _)
      let inc := (Standard.isRepresentedBy_parabolicHom i ν ∅).inclusionHom
        (Standard.isRepresentedBy_parabolicHom i ν (rootSet i ν J)) hOrder
      have hcomp : inc ≫ Standard.parabolicHom i ν (rootSet i ν J) =
          Standard.parabolicHom i ν ∅ :=
        SubgroupFunctor.IsRepresentedBy.inclusionHom_comp _ _ _
      exact IsIwasawaCompact.of_comp inc (hcomp.symm ▸ hK)
    exact ⟨hf.symm ▸ hStd P₁, hg'.symm ▸ hStd Q₁⟩
  · let e := G.innerIso n.val
    have hLevi := standardLeviTwistedIntersection F G hG T i hi ν hν CM cs hcs
    have hL₁ := hLevi Q P w hmin n rfl
    have hL₂ := hLevi P Q w⁻¹ hminInv n⁻¹ rfl
    rw [Subgroup.coe_inv, G.innerIso_inv_hom] at hL₂
    have hEq : (standardLevi i ν (rootSet i ν Q₁)).comap e.hom =
        standardLevi i ν (rootSet i ν P₁) := by
      change standardLevi i ν (rootSet i ν Q) ⊓
        (standardLevi i ν (rootSet i ν P)).comap e.inv =
          standardLevi i ν (rootSet i ν Q₁) at hL₂
      rw [← hL₂, SubgroupFunctor.comap_inf, ← SubgroupFunctor.comap_comp,
        e.hom_inv_id, SubgroupFunctor.comap_id, ← hL₁]
      apply SubgroupFunctor.ext
      intro X
      exact inf_comm _ _
    let eL := SubgroupFunctor.IsRepresentedBy.isoOfComap
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν P₁))
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν Q₁)) e hEq
    refine ⟨eL.inv, ⟨inferInstance, ?_⟩⟩
    rw [Standard.leviToParabolic_comp, ← Category.assoc, Standard.leviToParabolic_comp]
    exact SubgroupFunctor.IsRepresentedBy.isoOfComap_inv_comp _ _ _ _

/-- The rational geometric-lemma subgroups are the images of canonical nested
standard parabolics, with Iwasawa coverage inherited from the minimal one. -/
theorem eisensteinGeometricLemmaDatum : EisensteinGeometricLemmaDatumStatement.{u} := by
  intro F _ _ G _ hG T i _ hi ν hν P Q n hpos hinvpos
  obtain ⟨-, -, CM, cs, hcs⟩ := relativeWeylCoxeter F G hG T i hi ν hν
  let w : relativeWeylGroup i := QuotientGroup.mk n
  have hmin : IsMinimal cs Q P w := by
    apply ((minimalityLengthCriterion_proof cs) Q P w).mpr
    constructor
    · intro a ha
      have h := (hcs.2.2.1 w⁻¹ a).mpr (hinvpos a ((val_mem_rootSet i ν Q a).mpr ha))
      rw [← cs.length_inv (w⁻¹ * cs.simple a), mul_inv_rev,
        CoxeterSystem.inv_simple, inv_inv, cs.length_inv] at h
      exact h
    · intro a ha
      exact (hcs.2.2.1 w a).mpr (hpos a ((val_mem_rootSet i ν P a).mpr ha))
  obtain ⟨f, g', hf, hg', hgeom, hK, -⟩ :=
    eisensteinGeometricLemmaDatum_of_minimal F G hG T i hi ν hν cs hcs P Q n hmin
  exact ⟨_, _, intersectionSubset_subset cs Q P w, intersectionSubset_subset cs P Q w⁻¹,
    f, g', hf, hg', hgeom, hK⟩

end Langlands.Global
