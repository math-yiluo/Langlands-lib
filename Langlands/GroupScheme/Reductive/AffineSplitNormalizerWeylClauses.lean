import Langlands.GroupScheme.Reductive.AffineSplitNormalizerWeylStatement
import Langlands.GroupScheme.Torus.MaximalSelfCentralizingDescent
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Rational.TorusNormalizerRigidity
import Langlands.GroupScheme.Rational.NormalizerGaloisAction
import Langlands.GroupScheme.Rational.CrossTorusWeylTransport
import Langlands.GroupScheme.AlgebraicFundamentalGroupWeyl
import Langlands.GroupScheme.Torus.WeylGroupSchemeFibreCardinality
import Langlands.GroupScheme.Reductive.BaseChange

/-! # Clauses of the normalizer–Weyl exact sequence for a split maximal torus -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineSplitNormalizerWeyl

/-- A point `n ∈ G(S)` *induces* an automorphism `w` of the coordinate root datum when
conjugation by `n` normalizes the split torus through an automorphism `σ` whose pullback on
characters is `w`, i.e. `χ_m ∘ σ = χ_{w • m}` on all points. This is the predicate `Induces`
of `AffineSplitNormalizerWeylStatement`, over an arbitrary base scheme. -/
def Induces {S : Scheme.{u}} {G : GroupScheme S} {I : Type u} [Fintype I]
    (i : splitTorus S I ⟶ G) {J : Type*} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (n : Over.mk (𝟙 S) ⟶ G.X) (w : RootPairing.Aut P) : Prop :=
  ∃ σ : splitTorus.commGroupScheme S I ≅ splitTorus.commGroupScheme S I,
    IsNormalizingPoint (T := splitTorus.commGroupScheme S I) i n σ ∧
      ∀ (U : Over S) (x : U ⟶ (splitTorus S I).X) (m : I → ℤ),
        ∏ j, splitTorus.pointsEquiv I U (x ≫ (CommGroupScheme.groupHom σ.hom).hom.hom) j ^ m j =
          ∏ j, splitTorus.pointsEquiv I U x j ^ (w • m) j

/-- Clause 3: a point of `G(S)` centralizing a fibrewise maximal closed split torus is a
point of the torus. -/
theorem exists_eq_of_mem_centralizerPoints
    {S : Scheme.{u}} {G : GroupScheme S} (hG : IsReductive G)
    {I : Type u} [Finite I] (i : splitTorus S I ⟶ G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) i)
    {n : Over.mk (𝟙 S) ⟶ G.X}
    (hn : n ∈ centralizerPoints (T := splitTorus.commGroupScheme S I) i) :
    ∃ t : Over.mk (𝟙 S) ⟶ (splitTorus S I).X, n = t ≫ i.hom.hom := by
  have h := splitTorusCentralizer_eq_range_of_fibrewiseMaximal hG
    (T := splitTorus.commGroupScheme S I) (isSplitTorus_splitTorus I) i hi hmax
  have hn' : n ∈ (torusCentralizer (T := splitTorus.commGroupScheme S I) i).carrier
      (Over.mk (𝟙 S)) :=
    (mem_torusCentralizer_base_iff (T := splitTorus.commGroupScheme S I) i n).mpr hn
  rw [h] at hn'
  obtain ⟨t, ht⟩ := SubgroupFunctor.mem_range.mp hn'
  exact ⟨t, ht.symm⟩

/-! ### Clause 2 -/

/-- An integer power of a finite sum of exponents is the product of the powers. -/
theorem zpow_finsetSum {M : Type*} [CommGroup M] (a : M) {β : Type*} (s : Finset β)
    (f : β → ℤ) : a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]

/-- The character `χ_m` of the monomial map of `M` is the character `χ_{m M}`. -/
theorem prod_powUnits_zpow {I : Type u} [Fintype I] {A : Type u} [CommRing A]
    (M : Matrix I I ℤ) (y : I → Aˣ) (m : I → ℤ) :
    ∏ j, splitTorus.powUnits M y j ^ m j = ∏ j, y j ^ Matrix.vecMul m M j := by
  calc ∏ j, splitTorus.powUnits M y j ^ m j = ∏ j, ∏ l, y l ^ (M j l * m j) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [splitTorus.powUnits, ← Finset.prod_zpow]
        exact Finset.prod_congr rfl fun l _ => (zpow_mul _ _ _).symm
    _ = ∏ l, ∏ j, y l ^ (M j l * m j) := Finset.prod_comm
    _ = ∏ l, y l ^ Matrix.vecMul m M l := by
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [Matrix.vecMul, dotProduct, zpow_finsetSum]
        exact Finset.prod_congr rfl fun j _ => by rw [mul_comm]

/-- Over a connected base, a point normalizing a split torus acts on its points by the
monomial map of one exponent matrix. -/
theorem exists_matrix_of_isNormalizingPoint
    {S : Scheme.{u}} [ConnectedSpace S] {G : GroupScheme S} {I : Type u} [Fintype I]
    [DecidableEq I] (i : splitTorus S I ⟶ G) [Mono i.hom.hom.left]
    {n : Over.mk (𝟙 S) ⟶ G.X}
    {σ : splitTorus.commGroupScheme S I ≅ splitTorus.commGroupScheme S I}
    (hn : IsNormalizingPoint (T := splitTorus.commGroupScheme S I) i n σ) :
    ∃ M : Matrix I I ℤ, ∀ (U : Over S) (x : U ⟶ (splitTorus S I).X),
      splitTorus.pointsEquiv I U (x ≫ (CommGroupScheme.groupHom σ.hom).hom.hom) =
        splitTorus.powUnits M (splitTorus.pointsEquiv I U x) := by
  have hg : n ∈ (torusNormalizer (T := splitTorus.commGroupScheme S I) i).carrier
      (Over.mk (𝟙 S)) :=
    normalizerPoints_le_torusNormalizer (T := splitTorus.commGroupScheme S I) i ⟨σ, hn⟩
  have : ConnectedSpace (Over.mk (𝟙 S)).left := ‹ConnectedSpace S›
  obtain ⟨M, hM⟩ := TorusConjugation.exists_actsBy_of_connected
    (T := splitTorus.commGroupScheme S I) (Iso.refl (splitTorus S I)) hg
  refine ⟨M, fun U x => ?_⟩
  let a : U ⟶ Over.mk (𝟙 S) := Over.homMk U.hom (by simp)
  have h1 := hM U a (splitTorus.pointsEquiv I U x)
  rw [Category.comp_id] at h1
  have h2 := TorusConjugation.conjUnits_spec (Iso.refl _) hg a (splitTorus.pointsEquiv I U x)
  rw [h1] at h2
  have h3 := hn.conj_comp U x
  rw [← comp_eq_constantPoint a n] at h3
  have hx : TorusConjugation.unitsPoint (T := splitTorus.commGroupScheme S I) i
      (Iso.refl _) U (splitTorus.pointsEquiv I U x) = x ≫ i.hom.hom := by
    simp [TorusConjugation.unitsPoint]
  rw [hx, h3] at h2
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have h4 : x ≫ (CommGroupScheme.groupHom σ.hom).hom.hom =
      (splitTorus.pointsEquiv I U).symm
        (splitTorus.powUnits M (splitTorus.pointsEquiv I U x)) := by
    rw [TorusConjugation.unitsPoint] at h2
    simpa using (cancel_mono i.hom.hom).1 h2
  rw [h4, MulEquiv.apply_symm_apply]

/-- A torus endomorphism acting on points by the monomial map of `M` pulls the exponent
character `χ_m` back to `χ_{m M}`. -/
theorem comp_exponentCharacter_of_powUnits {S : Scheme.{u}} {I : Type u} [Fintype I]
    (f : splitTorus.commGroupScheme S I ⟶ splitTorus.commGroupScheme S I) (M : Matrix I I ℤ)
    (hM : ∀ (U : Over S) (x : U ⟶ (splitTorus S I).X),
      splitTorus.pointsEquiv I U (x ≫ (CommGroupScheme.groupHom f).hom.hom) =
        splitTorus.powUnits M (splitTorus.pointsEquiv I U x)) (m : I → ℤ) :
    f ≫ splitTorus.exponentCharacter S I m =
      splitTorus.exponentCharacter S I (Matrix.vecMul m M) := by
  refine CommGroupScheme.hom_ext_points fun U x => ?_
  apply (Gm.pointsEquiv S U).injective
  rw [comp_groupHom_comp, splitTorus.pointsEquiv_exponentCharacter,
    splitTorus.pointsEquiv_exponentCharacter, hM, prod_powUnits_zpow]

/-- If a point normalizing the split torus acts on it by the monomial map of `M`, then
some element `w` of the Weyl group satisfies `w • m = m M` for every exponent vector `m`.
The element is found on the fibre over any field `k` over `R`. -/
theorem exists_weylGroup_vecMul {R : Type u} [CommRing R] (k : Type u) [Field k]
    [Algebra R k] {G : GroupScheme (Spec (CommRingCat.of R))} (hG : IsReductive G)
    {I : Type u} [Fintype I] [DecidableEq I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : haveI := hG.isAffineHom; IsFibrewiseRootDatumOf I G i P)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X}
    {σ : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ≅
      splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I}
    (hn : IsNormalizingPoint (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I)
      i n σ)
    (M : Matrix I I ℤ)
    (hM : ∀ (U : Over (Spec (CommRingCat.of R)))
      (x : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X),
      splitTorus.pointsEquiv I U (x ≫ (CommGroupScheme.groupHom σ.hom).hom.hom) =
        splitTorus.powUnits M (splitTorus.pointsEquiv I U x)) :
    ∃ w ∈ P.weylGroup, ∀ m, w • m = Matrix.vecMul m M := by
  have := hG.isAffineHom
  have := hG.smooth
  have hR := comp_exponentCharacter_of_powUnits σ.hom M hM
  have hsq : (GroupScheme.baseChange (algebraBaseMap R k)).map i ≫
      (Iso.refl ((GroupScheme.baseChange (algebraBaseMap R k)).obj G)).hom =
      CommGroupScheme.groupHom (splitTorus.commBaseChangeIso (algebraBaseMap R k) I).hom ≫
        splitTorus.baseChangeHom (K := k) G I i := by
    rw [Iso.refl_hom, Category.comp_id]
    change _ = (splitTorus.baseChangeIso (algebraBaseMap R k) I).hom ≫
      (splitTorus.baseChangeIso (algebraBaseMap R k) I).inv ≫
        (GroupScheme.baseChange (algebraBaseMap R k)).map i
    rw [Iso.hom_inv_id_assoc]
  have h1 : IsNormalizingPoint
      (T := (CommGroupScheme.baseChange (algebraBaseMap R k)).obj
        (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I))
      ((GroupScheme.baseChange (algebraBaseMap R k)).map i)
      (baseChangeBasePoint (algebraBaseMap R k) G n⁻¹)
      ((CommGroupScheme.baseChange (algebraBaseMap R k)).mapIso σ.symm) :=
    hn.inv.baseChangeBasePoint (algebraBaseMap R k)
  -- The objects are given explicitly: leaving them to unification times out.
  have h2 := IsNormalizingPoint.transport
    (T := (CommGroupScheme.baseChange (algebraBaseMap R k)).obj
      (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I))
    (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
    (G := (GroupScheme.baseChange (algebraBaseMap R k)).obj G)
    (H := (GroupScheme.baseChange (algebraBaseMap R k)).obj G)
    (i := (GroupScheme.baseChange (algebraBaseMap R k)).map i)
    (j := splitTorus.baseChangeHom (K := k) G I i)
    (splitTorus.commBaseChangeIso (algebraBaseMap R k) I) (Iso.refl _) hsq h1
  obtain ⟨w', hw', hw'e⟩ :=
    AlgebraicFundamentalGroup.IsNormalizingPoint.exists_weylGroup
    (hG.isConnectedReductive_baseChange (algebraBaseMap R k)) (isSplitTorus_splitTorus I)
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax k) (hP.field k) h2
  have hK : ∀ m : I → ℤ,
      ((splitTorus.commBaseChangeIso (algebraBaseMap R k) I).symm ≪≫
          (CommGroupScheme.baseChange (algebraBaseMap R k)).mapIso σ.symm ≪≫
            splitTorus.commBaseChangeIso (algebraBaseMap R k) I).inv ≫
          splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m =
        splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (Matrix.vecMul m M) := by
    intro m
    simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc]
    rw [splitTorus.exponentCharacter_baseChange, characterLattice.baseChange_apply,
      ← Functor.map_comp_assoc, hR, ← characterLattice.baseChange_apply,
      ← splitTorus.exponentCharacter_baseChange, Iso.inv_hom_id_assoc]
  refine ⟨((rootDatumWeylGroupEquiv (CoordinateRootDatum.fieldRealizationEquiv k P)).symm
      ⟨w', hw'⟩ : P.weylGroup),
    ((rootDatumWeylGroupEquiv (CoordinateRootDatum.fieldRealizationEquiv k P)).symm
      ⟨w', hw'⟩).property, fun m => ?_⟩
  have hs : (CoordinateRootDatum.fieldRealizationEquiv k P).symm.weightEquiv =
      (CoordinateRootDatum.fieldRealizationEquiv k P).weightEquiv.symm := by ext; rfl
  have hE : ∀ y : I → ℤ, (CoordinateRootDatum.fieldRealizationEquiv k P).weightEquiv y =
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I y :=
    CoordinateRootDatum.fieldRealizationEquiv_weightMap k P
  change (CoordinateRootDatum.fieldRealizationEquiv k P).symm.weightEquiv
    (w'.weightEquiv ((CoordinateRootDatum.fieldRealizationEquiv k P).symm.weightEquiv.symm m)) = _
  rw [hs, LinearEquiv.symm_symm, hw'e, hE, hK, ← hE, LinearEquiv.symm_apply_apply]

/-- Clause 2: over a connected affine base, every point normalizing the split maximal torus
induces an element of the Weyl group. -/
theorem exists_weylGroup_of_mem_normalizerPoints
    {R : Type u} [CommRing R] [ConnectedSpace (Spec (CommRingCat.of R))]
    {G : GroupScheme (Spec (CommRingCat.of R))} (hG : IsReductive G)
    {I : Type u} [Fintype I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    (hP : haveI := hG.isAffineHom; IsFibrewiseRootDatumOf I G i P)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X}
    (hn : n ∈ normalizerPoints (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i) :
    ∃ w ∈ P.weylGroup, Induces i n w := by
  classical
  obtain ⟨σ, hσ⟩ := (mem_normalizerPoints (T := splitTorus.commGroupScheme _ I) i).1 hn
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom.left := inferInstance
  obtain ⟨M, hM⟩ := exists_matrix_of_isNormalizingPoint i hσ
  have : Nontrivial R := by
    obtain ⟨p⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of R)))
    exact PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨p⟩
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal R
  let := Ideal.Quotient.field 𝔪
  obtain ⟨w, hw, hwm⟩ := exists_weylGroup_vecMul (R ⧸ 𝔪) hG i hmax hP hσ M hM
  refine ⟨w, hw, ?_⟩
  unfold Induces
  exact ⟨σ, hσ, fun U x m => by rw [hM, prod_powUnits_zpow, hwm]⟩

end AffineSplitNormalizerWeyl

end Langlands.GroupScheme
