import Langlands.GroupScheme.Reductive.FibrewiseRootDatumAssembly
import Langlands.GroupScheme.Torus.IdentityTransporterEtaleLift
import Langlands.GroupScheme.Torus.ExponentHomomorphisms
import Langlands.GroupScheme.Torus.WeylImageFinite
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.RelativeTransporterSmooth
import Langlands.GroupScheme.Reductive.LocalSplitRootDatumExistenceStatement
import Langlands.GroupScheme.Reductive.RootDatumStatement

/-! # Transport of coordinate normalizing points between field fibres -/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section NormalizingTransporter

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
  {i : T.toGrp ⟶ G} {n : Over.mk (𝟙 S) ⟶ G.X} {σ : T ≅ T}

/-- A base point that transports `σ ≫ i` to `i` on all test schemes normalizes `i`
through `σ`. This is the converse of `IsNormalizingPoint.isTransporter`. -/
theorem IsNormalizingPoint.of_isTransporter
    (h : PointwiseSchemeAction.IsTransporter (CommGroupScheme.groupHom σ.hom ≫ i) i n) :
    IsNormalizingPoint i n σ := by
  apply Grp.hom_ext
  let a : T.X ⟶ Over.mk (𝟙 S) := Over.homMk T.X.hom (by simp)
  have hc : G.constantPoint n T.X = a ≫ n := rfl
  have he := h T.X a (𝟙 T.X)
  rw [Category.id_comp, Category.id_comp, ← hc] at he
  change i.hom.hom ≫ (G.innerIso n).hom.hom.hom = (CommGroupScheme.groupHom σ.hom ≫ i).hom.hom
  rw [G.comp_innerIso_hom, ← he, mul_inv_cancel_right]

theorem isNormalizingPoint_iff_isTransporter :
    IsNormalizingPoint i n σ ↔
      PointwiseSchemeAction.IsTransporter (CommGroupScheme.groupHom σ.hom ≫ i) i n :=
  ⟨IsNormalizingPoint.isTransporter, IsNormalizingPoint.of_isTransporter⟩

end NormalizingTransporter

namespace PointwiseSchemeAction

variable {S : Scheme.{u}} {H H' G : GroupScheme S} {i₁ i₂ : H ⟶ G}
  {T : Over S} {g : T ⟶ G.X}

/-- Precomposition with an isomorphism does not change the transporter relation. -/
theorem isTransporter_precomp_iso_iff (e : H' ≅ H) :
    IsTransporter (e.hom ≫ i₁) (e.hom ≫ i₂) g ↔ IsTransporter i₁ i₂ g := by
  constructor
  · intro h
    simpa only [Iso.inv_hom_id_assoc] using h.precomp e.inv
  · intro h
    exact h.precomp e.hom

end PointwiseSchemeAction

namespace splitTorus

variable {S : Scheme.{u}} (I : Type u) [Fintype I] [DecidableEq I]

theorem exponentCharacter_single (j : I) :
    exponentCharacter S I (Pi.single j 1) = proj S I j := by
  simp [exponentCharacter, Pi.single_apply]

/-- A torus automorphism whose character action is the fixed-exponent action of an
integral coordinate automorphism `C` is the inverse of the exponent automorphism of `C`. -/
theorem eq_exponentCommIso_symm (C : (I → ℤ) ≃ₗ[ℤ] (I → ℤ))
    (σ : commGroupScheme S I ≅ commGroupScheme S I)
    (hσ : ∀ m, characterAut σ (exponentCharacter S I m) = exponentCharacter S I (C m)) :
    σ = (exponentCommIso S I C).symm := by
  have hinv : σ.inv = (exponentCommIso S I C).hom := by
    apply hom_ext_projections S I
    intro j
    rw [← exponentCharacter_single]
    change characterAut σ _ = _
    rw [hσ]
    exact (exponentHom_comp_exponentCharacter S I I C.toLinearMap _).symm
  apply Iso.ext
  exact (Iso.inv_eq_inv σ (exponentCommIso S I C).symm).mp hinv

theorem characterAut_exponentCommIso_symm (C : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)) (m : I → ℤ) :
    characterAut (exponentCommIso S I C).symm (exponentCharacter S I m) =
      exponentCharacter S I (C m) :=
  exponentHom_comp_exponentCharacter S I I C.toLinearMap m

end splitTorus

/-! ### Transport of the transporter relation between field fibres -/

namespace LocalSplitCorootTransport

open PointwiseSchemeAction

variable {R : Type u} [CommRing R] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of R)))
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (C : (I → ℤ) ≃ₗ[ℤ] (I → ℤ))

/-- The coordinate twist `(exponentIso C).inv ≫ i` commutes with base change. -/
theorem exponentIso_inv_comp_baseChangeHom (K : Type u) [CommRing K] [Algebra R K] :
    (splitTorus.exponentIso (Spec (CommRingCat.of K)) I C).inv ≫
        splitTorus.baseChangeHom (K := K) G I i =
      (splitTorus.baseChangeIso (algebraBaseMap R K) I).inv ≫
        (baseChange (algebraBaseMap R K)).map
          ((splitTorus.exponentIso (Spec (CommRingCat.of R)) I C).inv ≫ i) := by
  have h := splitTorus.exponentIso_baseChange (Spec (CommRingCat.of R)) I
    (algebraBaseMap R K) C.symm
  have h' : (splitTorus.exponentIso (Spec (CommRingCat.of K)) I C).inv ≫
      (splitTorus.baseChangeIso (algebraBaseMap R K) I).inv =
      (splitTorus.baseChangeIso (algebraBaseMap R K) I).inv ≫
        (baseChange (algebraBaseMap R K)).map
          (splitTorus.exponentIso (Spec (CommRingCat.of R)) I C).inv := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact h
  rw [splitTorus.baseChangeHom, ← Category.assoc, h', Category.assoc, Functor.map_comp]

/-- The twisted transporter relation on a field fibre is the same relation for the
corresponding point of the original group. -/
theorem isTransporter_baseChangeHom_iff (K : Type u) [CommRing K] [Algebra R K]
    {T : Over (Spec (CommRingCat.of K))}
    (n : T ⟶ ((baseChange (algebraBaseMap R K)).obj G).X) :
    IsTransporter ((splitTorus.exponentIso (Spec (CommRingCat.of K)) I C).inv ≫
        splitTorus.baseChangeHom (K := K) G I i) (splitTorus.baseChangeHom (K := K) G I i) n ↔
      IsTransporter ((splitTorus.exponentIso (Spec (CommRingCat.of R)) I C).inv ≫ i) i
        (Langlands.GroupScheme.baseChangePointsEquiv (algebraBaseMap R K) G T n) := by
  rw [exponentIso_inv_comp_baseChangeHom, splitTorus.baseChangeHom]
  refine (isTransporter_precomp_iso_iff
    (splitTorus.baseChangeIso (algebraBaseMap R K) I).symm).trans ⟨fun h => ?_, fun h => ?_⟩
  · exact h.baseChangePointsEquiv _
  · exact IsTransporter.baseChange_of_equiv _ _ _ n h

/-- The coordinate automorphism `C` is realized over the `R`-field `K` when some
`K`-point of `G`, over `Spec R`, transports `(exponentIso C).inv ≫ i` to `i`. -/
def IsRealizedAt (K : Type u) [CommRing K] [Algebra R K] : Prop :=
  ∃ g : Over.mk (algebraBaseMap R K) ⟶ G.X,
    IsTransporter ((splitTorus.exponentIso (Spec (CommRingCat.of R)) I C).inv ≫ i) i g

/-- The comparison of the two descriptions of `Spec K` over `Spec R`. -/
def overComparison (K : Type u) [CommRing K] [Algebra R K] :
    Over.mk (algebraBaseMap R K) ⟶
      (Over.map (algebraBaseMap R K)).obj (Over.mk (𝟙 (Spec (CommRingCat.of K)))) :=
  Over.homMk (𝟙 _) (by simp)

/-- The inverse comparison of the two descriptions of `Spec K` over `Spec R`. -/
def overComparisonInv (K : Type u) [CommRing K] [Algebra R K] :
    (Over.map (algebraBaseMap R K)).obj (Over.mk (𝟙 (Spec (CommRingCat.of K)))) ⟶
      Over.mk (algebraBaseMap R K) :=
  Over.homMk (𝟙 _) (by simp)

/-- A normalizing point on the field fibre whose automorphism acts on fixed-exponent
characters by `C` realizes `C`. -/
theorem isRealizedAt_iff (K : Type u) [Field K] [Algebra R K] :
    IsRealizedAt I G i C K ↔
      ∃ n, IsNormalizingPoint (splitTorus.baseChangeHom (K := K) G I i) n
        (splitTorus.exponentCommIso (Spec (CommRingCat.of K)) I C).symm := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨(Langlands.GroupScheme.baseChangePointsEquiv (algebraBaseMap R K) G _).symm
      (overComparisonInv K ≫ g), ?_⟩
    apply IsNormalizingPoint.of_isTransporter
    change IsTransporter ((splitTorus.exponentIso (Spec (CommRingCat.of K)) I C).inv ≫
        splitTorus.baseChangeHom (K := K) G I i) _ _
    rw [isTransporter_baseChangeHom_iff, MulEquiv.apply_symm_apply]
    exact hg.restrict _
  · rintro ⟨n, hn⟩
    refine ⟨overComparison K ≫
      Langlands.GroupScheme.baseChangePointsEquiv (algebraBaseMap R K) G _ n, ?_⟩
    have h := hn.isTransporter
    change IsTransporter ((splitTorus.exponentIso (Spec (CommRingCat.of K)) I C).inv ≫
        splitTorus.baseChangeHom (K := K) G I i) _ _ at h
    rw [isTransporter_baseChangeHom_iff] at h
    exact h.restrict _

/-- Realizations restrict along an extension of `R`-algebras. -/
theorem IsRealizedAt.restrict {l L : Type u} [CommRing l] [CommRing L] [Algebra R l]
    [Algebra l L] [Algebra R L] [IsScalarTower R l L]
    (h : IsRealizedAt I G i C l) : IsRealizedAt I G i C L := by
  obtain ⟨g, hg⟩ := h
  refine ⟨Over.homMk (V := Over.mk (algebraBaseMap R l)) (algebraBaseMap l L) ?_ ≫ g,
    hg.restrict _⟩
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- The lifting property of flat schemes over a local ring: a point over the closed
point yields, for every field `l` over the base, a point with values in an extension
field of `l`. -/
def FlatClosedPointLiftProperty : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] (x : X),
    f x = IsLocalRing.closedPoint R →
    ∀ (l : Type u) [Field l] [Algebra R l],
      ∃ (L : Type u) (_ : Field L) (_ : Algebra l L) (g : Spec (CommRingCat.of L) ⟶ X),
        g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap l L)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R l))

/-- A realization on the residue field of a local base spreads to an extension of
every field over the base, through the smooth transporter scheme. -/
theorem IsRealizedAt.exists_extension [IsLocalRing R] [IsAffineHom G.X.hom]
    (hG : Smooth G.X.hom) (hlift : FlatClosedPointLiftProperty.{u})
    (h : IsRealizedAt I G i C (IsLocalRing.ResidueField R))
    (l : Type u) [Field l] [Algebra R l] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra R L) (_ : Algebra l L)
      (_ : IsScalarTower R l L), IsRealizedAt I G i C L := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let d := Diagonalizable.splitIso (CommRingCat.of R) (AddEquiv.refl (I → ℤ))
  let j₁ := d.hom ≫ (splitTorus.exponentIso (Spec (CommRingCat.of R)) I C).inv ≫ i
  let j₂ := d.hom ≫ i
  obtain ⟨g, hg⟩ := h
  let A := CommAlgCat.of (CommRingCat.of R) (IsLocalRing.ResidueField R)
  let c : (algSpec (CommRingCat.of R)).obj (Opposite.op A) ⟶
      Over.mk (algebraBaseMap R (IsLocalRing.ResidueField R)) :=
    Over.homMk (𝟙 _) (by rw [Category.id_comp]; rfl)
  obtain ⟨y, -⟩ := (exists_relativeTransporter_factor_iff j₁ j₂ (c ≫ g)).mpr
    ((isTransporter_precomp_iso_iff d).mpr (hg.restrict c))
  let X := relativeTransporterScheme j₁ j₂
  have : Smooth X.hom := smooth_relativeTransporterScheme j₁ j₂ hG
  have : Flat X.hom := inferInstance
  have hx : X.hom (y.left (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) =
      IsLocalRing.closedPoint R := by
    rw [← Scheme.Hom.comp_apply, Over.w y]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  obtain ⟨L, _, _, g', hg'⟩ := hlift R X.left X.hom _ hx l
  let _ : Algebra R L := ((algebraMap l L).comp (algebraMap R l)).toAlgebra
  have : IsScalarTower R l L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  let z : Over.mk (algebraBaseMap R L) ⟶ X := Over.homMk g' (by
    change g' ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap R L))
    rw [hg', ← Spec.map_comp]
    rfl)
  exact ⟨z ≫ relativeTransporterHom j₁ j₂, (isTransporter_precomp_iso_iff d).mp
    ((relativeTransporterHom_isTransporter j₁ j₂).restrict z)⟩

/-- Conjugation of character-lattice automorphisms by the fixed-exponent coordinates. -/
def coordinateConj (K : Type u) [Field K] :
    (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I) ≃ₗ[ℤ]
        characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I)) →*
      ((I → ℤ) ≃ₗ[ℤ] (I → ℤ)) where
  toFun f := ((splitTorus.characterLatticeEquiv K I).symm.toIntLinearEquiv.trans f).trans
    (splitTorus.characterLatticeEquiv K I).toIntLinearEquiv
  map_one' := by
    ext m j
    simp
  map_mul' f g := by
    ext m j
    simp

theorem coordinateConj_characterAut (K : Type u) [Field K] :
    coordinateConj I K
        (characterAut (splitTorus.exponentCommIso (Spec (CommRingCat.of K)) I C).symm) = C := by
  ext m : 1
  change splitTorus.characterLatticeEquiv K I
      (characterAut (splitTorus.exponentCommIso (Spec (CommRingCat.of K)) I C).symm
        ((splitTorus.characterLatticeEquiv K I).symm m)) = C m
  rw [← splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
    splitTorus.characterAut_exponentCommIso_symm,
    splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm, AddEquiv.apply_symm_apply]

local instance fieldFibreAffine [IsAffineHom G.X.hom] {K : Type u} [Field K] [Algebra R K] :
    IsAffineHom ((baseChange (algebraBaseMap R K)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R K)))

local instance fieldFibreLocallyOfFiniteType [LocallyOfFiniteType G.X.hom]
    {K : Type u} [Field K] [Algebra R K] :
    LocallyOfFiniteType ((baseChange (algebraBaseMap R K)).obj G).X.hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom (algebraBaseMap R K)))

/-- Two automorphisms of a closed split torus in an affine algebraic group that are
realized by normalizing points have a product of finite order on characters: both lie
in the finite Weyl image. -/
theorem isOfFinOrder_characterAut_mul {k : Type u} [Field k]
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    [LocallyOfFiniteType H.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ H) (hj : IsClosedSubgroup j)
    {σ₁ σ₂ : T ≅ T} {n₁ n₂ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X}
    (h₁ : IsNormalizingPoint j n₁ σ₁) (h₂ : IsNormalizingPoint j n₂ σ₂) :
    IsOfFinOrder (characterAut σ₁ * characterAut σ₂) := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Finite (weylImage j) := splitTorusWeylImageFinite k H T hT j hj
  let m₁ : normalizerPoints j := ⟨n₁, σ₁, h₁⟩
  let m₂ : normalizerPoints j := ⟨n₂, σ₂, h₂⟩
  have hs₁ : weylAction j m₁ = characterAut σ₁ := by
    ext χ
    exact weylAction_eq j (n := m₁) (σ := σ₁) h₁ χ
  have hs₂ : weylAction j m₂ = characterAut σ₂ := by
    ext χ
    exact weylAction_eq j (n := m₂) (σ := σ₂) h₂ χ
  let a : weylImage j := ⟨weylAction j m₁, m₁, rfl⟩
  let b : weylImage j := ⟨weylAction j m₂, m₂, rfl⟩
  have h := (weylImage j).subtype.isOfFinOrder (isOfFinOrder_of_finite (a * b))
  rw [map_mul, Subgroup.coe_subtype] at h
  change IsOfFinOrder (weylAction j m₁ * weylAction j m₂) at h
  rwa [hs₁, hs₂] at h

/-- Two coordinate automorphisms realized on one field fibre, on which the torus is
closed, have a product of finite order: both lie in the finite Weyl image there. -/
theorem isOfFinOrder_mul_of_isRealizedAt [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (K : Type u) [Field K] [Algebra R K]
    (hi : IsClosedSubgroup (splitTorus.baseChangeHom (K := K) G I i))
    {C₁ C₂ : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)}
    (h₁ : IsRealizedAt I G i C₁ K) (h₂ : IsRealizedAt I G i C₂ K) :
    IsOfFinOrder (C₁ * C₂) := by
  obtain ⟨n₁, hn₁⟩ := (isRealizedAt_iff I G i C₁ K).mp h₁
  obtain ⟨n₂, hn₂⟩ := (isRealizedAt_iff I G i C₂ K).mp h₂
  have key := (coordinateConj I K).isOfFinOrder
    (isOfFinOrder_characterAut_mul (T := splitTorus.commGroupScheme _ I)
      (isSplitTorus_splitTorus I) _ hi hn₁ hn₂)
  rwa [map_mul, coordinateConj_characterAut, coordinateConj_characterAut] at key

/-- Each reflection of an actual realized coordinate datum on a field fibre is realized
on that fibre. -/
theorem isRealizedAt_reflection [IsAffineHom G.X.hom] (k : Type u) [Field k] [Algebra R k]
    {J : Type v} (P : RootDatum J (I → ℤ) (I → ℤ))
    (hP : IsRootDatumOf (splitTorus.baseChangeHom (K := k) G I i)
      (CoordinateRootDatum.fieldRealization k P)) (j : J) :
    IsRealizedAt I G i (P.reflection j) k := by
  obtain ⟨n, σ, hn, hσ⟩ := hP.2.2 j
  have hσ' : σ = (splitTorus.exponentCommIso (Spec (CommRingCat.of k)) I (P.reflection j)).symm :=
    splitTorus.eq_exponentCommIso_symm I _ σ fun m => by
      rw [hσ, CoordinateRootDatum.fieldRealization_reflection_exponentCharacter]
  exact (isRealizedAt_iff I G i (P.reflection j) k).mpr ⟨n, hσ' ▸ hn⟩

end LocalSplitCorootTransport

end Langlands.GroupScheme

/-! ### Identity-lattice equivalences from finite-order reflection products -/

namespace Langlands.LinearAlgebra

variable {M : Type u} [AddCommGroup M] {N : Type v} [AddCommGroup N]
  {J : Type w} {J' : Type*} (P : RootDatum J M N) (Q : RootDatum J' M N)

/-- Equal roots of two root data with the same pairing have equal coroots when the
product of their two reflections has finite order. -/
theorem coroot_eq_of_isOfFinOrder_mul
    (hpair : P.toLinearMap = Q.toLinearMap)
    {j : J} {j' : J'} (hroot : P.root j = Q.root j')
    (horder : IsOfFinOrder (P.reflection j * Q.reflection j')) :
    P.coroot j = Q.coroot j' := by
  let f := P.toLinearMap.flip (P.coroot j)
  let g := P.toLinearMap.flip (Q.coroot j')
  have hf : f (P.root j) = 2 := P.root_coroot_two j
  have hg : g (P.root j) = 2 := by
    change P.toLinearMap (P.root j) (Q.coroot j') = 2
    rw [hpair, hroot]
    exact Q.root_coroot_two j'
  have heq := eq_functional_of_finiteOrder_reflections
    (P.root j) f g (P.reflection j) (Q.reflection j') hf hg
    (fun x => by
      rw [RootPairing.reflection_apply])
    (fun x => by
      rw [RootPairing.reflection_apply]
      change x - Q.toLinearMap x (Q.coroot j') • Q.root j' =
        x - P.toLinearMap x (Q.coroot j') • P.root j
      rw [hpair, hroot]) horder
  apply P.flip.toPerfPair.injective
  exact heq

/-- Full root-data equivalence with both lattice maps the identity, obtained from
equal pairings, equal root ranges, and finite order of the product of the two
reflections attached to each common root. -/
def rootDatumEquivOfFiniteOrderReflections
    (hpair : P.toLinearMap = Q.toLinearMap)
    (hroots : Set.range P.root = Set.range Q.root)
    (horder : ∀ (j : J) (j' : J'), P.root j = Q.root j' →
      IsOfFinOrder (P.reflection j * Q.reflection j')) : RootPairing.Equiv P Q where
  weightMap := LinearMap.id
  coweightMap := LinearMap.id
  indexEquiv := rootIndexEquivOfRangeEq P Q hroots
  weight_coweight_transpose := by
    ext n m
    change Q.toLinearMap m n = P.toLinearMap m n
    rw [hpair]
  root_weightMap := by
    funext j
    exact (rootIndexEquivOfRangeEq_root P Q hroots j).symm
  coroot_coweightMap := by
    funext j'
    change Q.coroot j' = P.coroot ((rootIndexEquivOfRangeEq P Q hroots).symm j')
    have hroot : P.root ((rootIndexEquivOfRangeEq P Q hroots).symm j') = Q.root j' := by
      have h := rootIndexEquivOfRangeEq_root P Q hroots
        ((rootIndexEquivOfRangeEq P Q hroots).symm j')
      simp only [Equiv.apply_symm_apply] at h
      exact h.symm
    exact (coroot_eq_of_isOfFinOrder_mul P Q hpair hroot (horder _ _ hroot)).symm
  bijective_weightMap := Function.bijective_id
  bijective_coweightMap := Function.bijective_id

@[simp]
theorem rootDatumEquivOfFiniteOrderReflections_weightMap
    (hpair : P.toLinearMap = Q.toLinearMap)
    (hroots : Set.range P.root = Set.range Q.root)
    (horder : ∀ (j : J) (j' : J'), P.root j = Q.root j' →
      IsOfFinOrder (P.reflection j * Q.reflection j')) :
    (rootDatumEquivOfFiniteOrderReflections P Q hpair hroots horder).toHom.weightMap =
      LinearMap.id := rfl

@[simp]
theorem rootDatumEquivOfFiniteOrderReflections_coweightMap
    (hpair : P.toLinearMap = Q.toLinearMap)
    (hroots : Set.range P.root = Set.range Q.root)
    (horder : ∀ (j : J) (j' : J'), P.root j = Q.root j' →
      IsOfFinOrder (P.reflection j * Q.reflection j')) :
    (rootDatumEquivOfFiniteOrderReflections P Q hpair hroots horder).toHom.coweightMap =
      LinearMap.id := rfl

end Langlands.LinearAlgebra

/-! ### Assembly over a local base -/

namespace Langlands.GroupScheme

namespace LocalSplitCorootTransport

variable {R : Type u} [CommRing R] [IsLocalRing R] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of R))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)

/-- A coordinate datum realized on the residue field is realized on every field fibre
on which some coordinate datum is realized, provided the torus is closed on all field
fibres and flat schemes over the local base lift closed-fibre points. -/
theorem isRootDatumOf_of_residueField (hlift : FlatClosedPointLiftProperty.{u})
    (hclosed : ∀ (K : Type u) [Field K] [Algebra R K],
      IsClosedSubgroup (splitTorus.baseChangeHom (K := K) G I i))
    {J : Type v} (P : RootDatum J (I → ℤ) (I → ℤ))
    (hP : IsRootDatumOf (splitTorus.baseChangeHom (K := IsLocalRing.ResidueField R) G I i)
      (CoordinateRootDatum.fieldRealization (IsLocalRing.ResidueField R) P))
    (l : Type u) [Field l] [Algebra R l] {J' : Type w} (Q : RootDatum J' (I → ℤ) (I → ℤ))
    (hQ : IsRootDatumOf (splitTorus.baseChangeHom (K := l) G I i)
      (CoordinateRootDatum.fieldRealization l Q)) :
    IsRootDatumOf (splitTorus.baseChangeHom (K := l) G I i)
      (CoordinateRootDatum.fieldRealization l P) := by
  have horder : ∀ (j' : J') (j : J), Q.root j' = P.root j →
      IsOfFinOrder (Q.reflection j' * P.reflection j) := by
    intro j' j _
    obtain ⟨L, _, _, _, _, hPL⟩ := (isRealizedAt_reflection I G i
      (IsLocalRing.ResidueField R) P hP j).exists_extension I G i _ inferInstance hlift l
    exact isOfFinOrder_mul_of_isRealizedAt I G i L (hclosed L)
      ((isRealizedAt_reflection I G i l Q hQ j').restrict I G i _ (l := l)) hPL
  let e := Langlands.LinearAlgebra.rootDatumEquivOfFiniteOrderReflections Q P
    (CoordinateRootDatum.pairing_eq_of_fields I G i l Q _ P hQ hP)
    (CoordinateRootDatum.rootRange_eq_of_fields I G i l Q _ P hQ hP) horder
  exact CoordinateRootDatum.isRootDatumOf_of_identityEquiv l hQ e rfl rfl

end LocalSplitCorootTransport

/-- The field root-datum existence theorem and the lifting property of flat schemes
over a local ring give common root data over a local base. -/
theorem localSplitFibrewiseRootDatumExistence_of_rootDatumExistence
    (hD : RootDatumExistenceStatement.{u})
    (hlift : LocalSplitCorootTransport.FlatClosedPointLiftProperty.{u}) :
    LocalSplitFibrewiseRootDatumExistenceStatement.{u} := by
  intro R _ _ G _ hG I _ i _ hmax
  classical
  have := hG.smooth
  have hmaxK : ∀ (k : Type u) [Field k] [Algebra R k],
      IsMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
        (splitTorus.baseChangeHom (K := k) G I i) :=
    fun k _ _ => splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax k
  have hfield : ∀ (k : Type u) [Field k] [Algebra R k],
      ∃ (J : Type u) (_ : Finite J)
        (P : RootDatum J
          (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I))
          (cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I))),
        IsRootDatumOf (splitTorus.baseChangeHom (K := k) G I i) P ∧ P.IsReduced :=
    fun k _ _ => hD k _ (hG.isConnectedReductive_algebraMap k)
      (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
      (isSplitTorus_splitTorus I) _ (hmaxK k)
  obtain ⟨J, hJ, P, hP, hred⟩ := hfield (IsLocalRing.ResidueField R)
  refine ⟨J, CoordinateRootDatum.ofField (IsLocalRing.ResidueField R) P, hJ,
    CoordinateRootDatum.ofField_isReduced hred, fun l _ _ => ?_⟩
  obtain ⟨J', _, Q, hQ, _⟩ := hfield l
  exact LocalSplitCorootTransport.isRootDatumOf_of_residueField I G i hlift
    (fun K _ _ => (hmaxK K).2.1) _
    (CoordinateRootDatum.isRootDatumOf_fieldRealization_ofField hP) l _
    (CoordinateRootDatum.isRootDatumOf_fieldRealization_ofField hQ)

end Langlands.GroupScheme
