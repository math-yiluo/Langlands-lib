import Langlands.GroupScheme.Rational.BruhatFactorizationStatement
import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.Rational.BruhatOpenCellReduction
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.FiniteEtaleImage

/-! # The all-test unipotent factorization for a Bruhat cell -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineLine

variable {S : Scheme.{u}} {K L : Type u} [Field K] [Field L]
    (f : Spec (CommRingCat.of K) ⟶ S) (r : K →+* L)

/-- A field extension of a field point of the base, as a test scheme over the base. -/
private abbrev relFieldTest : Over S := Over.mk (Spec.map (CommRingCat.ofHom r) ≫ f)

/-- The structure map from the extension field test to the field point. -/
private def relFieldBase : relFieldTest f r ⟶ Over.mk f :=
  Over.homMk (Spec.map (CommRingCat.ofHom r)) rfl

/-- Evaluation of the polynomial affine line over the field point at an element
of the extension field. -/
private def relFieldEvaluation (x : L) : relFieldTest f r ⟶ polynomialScheme f :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom r x))) (by
    change Spec.map _ ≫ Spec.map (polynomialC (CommRingCat.of K)) ≫ f = _
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext a
    simp)

/-- Evaluation followed by the product comparison is the point with the given
affine coordinate. -/
@[reassoc]
private theorem relFieldEvaluation_comp_polynomialPoint (x : L) :
    relFieldEvaluation f r x ≫ polynomialPoint f =
      lift (relFieldBase f r)
        ((homEquiv (relFieldTest f r)).symm ((Scheme.ΓSpecIso (CommRingCat.of L)).inv x)) := by
  rw [polynomialPoint, comp_lift]
  congr 1
  · apply Over.OverMorphism.ext
    change Spec.map _ ≫ Spec.map (polynomialC (CommRingCat.of K)) =
      Spec.map (CommRingCat.ofHom r)
    rw [← Spec.map_comp]
    congr 1
    ext a
    simp
  · apply hom_ext
    rw [homEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change (Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom r x))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv Polynomial.X) = _
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    simp

end AffineLine

namespace Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S} [IsSeparated G.X.hom]
    (χ : (Gm S).toGrp ⟶ G) {T U : Over S} {g : T ⟶ G.X}
    {e : T ⊗ AffineLine.scheme S ⟶ G.X} (he : IsOrbitExtension χ g e)
    (j : U ⟶ G.X) [IsOpenImmersion j.left] (hj : IsCocharacterStable χ j)

include he hj in
/-- Restricted to a field-valued point of the test scheme, an orbit extension whose
zero value factors through a cocharacter-stable open has its whole image in it. -/
private theorem fieldOrbit_range_subset {K : Type u} [Field K]
    (f : Spec (CommRingCat.of K) ⟶ S) (b : Over.mk f ⟶ T)
    (h0 : ∃ z : T ⟶ U, z ≫ j = evalZero e) :
    Set.range (b ▷ AffineLine.scheme S ≫ e).left ⊆ Set.range j.left := by
  let e' := b ▷ AffineLine.scheme S ≫ e
  have he' : IsOrbitExtension χ (b ≫ g) e' := he.whiskerRight χ b
  have hinv : AffineLine.IsScalarInvariantOpen
      ((AffineLine.polynomialPoint f ≫ e').left ⁻¹ᵁ j.left.opensRange) := by
    intro L _ r x a
    let V := AffineLine.relFieldTest f r
    let α : V ⟶ (Gm S).X := (Gm.pointsEquiv S V).symm
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom.toMonoidHom a)
    have hα : (Gm.pointsEquiv S V α : Γ(V.left, ⊤)) =
        (Scheme.ΓSpecIso (CommRingCat.of L)).inv a := by
      dsimp only [α]
      rw [MulEquiv.apply_symm_apply]
      rfl
    have hscale := he'.eval_scale χ (AffineLine.relFieldBase f r) α
      ((Scheme.ΓSpecIso (CommRingCat.of L)).inv x)
    have hm : (Scheme.ΓSpecIso (CommRingCat.of L)).inv (a * x) =
        (Scheme.ΓSpecIso (CommRingCat.of L)).inv a *
          (Scheme.ΓSpecIso (CommRingCat.of L)).inv x :=
      map_mul (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom (a : L) x
    rw [hα, ← hm] at hscale
    simp only [← AffineLine.relFieldEvaluation_comp_polynomialPoint_assoc] at hscale
    let y (t : L) := AffineLine.relFieldEvaluation f r t ≫ AffineLine.polynomialPoint f ≫ e'
    change (y ((a : L) * x)).left (⊥ : PrimeSpectrum L) ∈ j.left.opensRange ↔
      (y x).left (⊥ : PrimeSpectrum L) ∈ j.left.opensRange
    have hmem (v : V ⟶ G.X) : v.left (⊥ : PrimeSpectrum L) ∈ j.left.opensRange ↔
        ∃ z : V ⟶ U, z ≫ j = v := by
      constructor
      · intro hv
        have hr : Set.range v.left ⊆ Set.range j.left := by
          rintro _ ⟨p, rfl⟩
          have hp : (p : PrimeSpectrum L) = (⊥ : PrimeSpectrum L) :=
            @Subsingleton.elim (PrimeSpectrum L) _ p ⊥
          rw [hp]
          exact hv
        exact ⟨FiniteEtaleImage.liftOver j v hr, FiniteEtaleImage.liftOver_fac _ _ _⟩
      · rintro ⟨z, rfl⟩
        exact ⟨z.left (⊥ : PrimeSpectrum L), rfl⟩
    rw [hmem, hmem, ← show (α ≫ χ.hom.hom) * y x * (α ≫ χ.hom.hom)⁻¹ =
      y ((a : L) * x) from hscale]
    exact hj.factors_iff χ α (y x)
  obtain ⟨l, hl⟩ := h0
  have hzero : (AffineLine.polynomialPoint f ≫ e').left
      (AffineLine.fieldPoint (RingHom.id K) 0) ∈ j.left.opensRange := by
    have hz : AffineLine.polynomialZero f ≫ AffineLine.polynomialPoint f ≫ e' =
        b ≫ l ≫ j := by
      rw [← Category.assoc, AffineLine.polynomialZero_comp_polynomialPoint]
      change evalZero (b ▷ AffineLine.scheme S ≫ e) = _
      rw [evalZero_whiskerRight, hl]
    exact ⟨(b ≫ l).left (⊥ : PrimeSpectrum K),
      (congrArg (fun v => v.left (⊥ : PrimeSpectrum K)) hz).symm⟩
  have hr := AffineLine.range_subset_of_isScalarInvariantOpen j.left
    (AffineLine.polynomialPoint f ≫ e').left hinv hzero
  rintro _ ⟨x, rfl⟩
  apply hr
  refine ⟨(AffineLine.polynomialPointInv f).left x, ?_⟩
  have h := congrArg (fun a => a.left x)
    (AffineLine.polynomialPointInv_comp_polynomialPoint f)
  change (AffineLine.polynomialPoint f ≫ e').left ((AffineLine.polynomialPointInv f).left x) =
    e'.left x
  exact congrArg e'.left h

include he hj in
/-- If the zero value of an orbit extension factors through a cocharacter-stable
open, then so does the whole extension, over any test scheme. -/
private theorem IsOrbitExtension.exists_lift_of_cocharacterStable
    (h0 : ∃ z : T ⟶ U, z ≫ j = evalZero e) :
    ∃ l : T ⊗ AffineLine.scheme S ⟶ U, l ≫ j = e := by
  have hr : Set.range e.left ⊆ Set.range j.left := by
    rintro _ ⟨x, rfl⟩
    let X := T ⊗ AffineLine.scheme S
    let K := X.left.residueField x
    let r := X.left.fromSpecResidueField x
    let f := r ≫ X.hom
    let z : Over.mk f ⟶ X := Over.homMk r rfl
    let b := z ≫ fst T (AffineLine.scheme S)
    let q : Over.mk f ⟶ Over.mk f ⊗ AffineLine.scheme S :=
      lift (𝟙 _) (z ≫ snd T (AffineLine.scheme S))
    have hq : q ≫ b ▷ AffineLine.scheme S = z := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [q, b]
      · simp [q]
    apply fieldOrbit_range_subset χ he j hj f b h0
    refine ⟨q.left (IsLocalRing.closedPoint K), ?_⟩
    have h := congrArg (fun m => (m ≫ e).left (IsLocalRing.closedPoint K)) hq
    exact h.trans (congrArg e.left (Scheme.fromSpecResidueField_apply _ _))
  exact ⟨FiniteEtaleImage.liftOver j e hr, FiniteEtaleImage.liftOver_fac _ _ _⟩

end Dynamic


namespace BruhatFactorization

open Langlands.GroupScheme.Dynamic

/-- A test point of the product followed by the multiplication and the inclusion
of the common subgroup is the product of the two included factors. -/
private theorem comp_multiplication {S : Scheme.{u}} {G U A B : GroupScheme S}
    (u : U ⟶ G) (a : A ⟶ G) (b : B ⟶ G) {X : Over S}
    (t : X ⟶ (subgroupIntersection u a).X ⊗ (subgroupIntersection u b).X) :
    t ≫ multiplication u a b ≫ u.hom.hom =
      (t ≫ fst _ _ ≫ (subgroupIntersectionHom u a).hom.hom) *
        (t ≫ snd _ _ ≫ (subgroupIntersectionHom u b).hom.hom) := by
  simp only [multiplication, MonObj.mul_comp, MonObj.comp_mul, subgroupIntersectionHom,
    Grp.comp_hom_hom, Category.assoc]

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

set_option maxHeartbeats 600000 in
/-- The factorization for two cocharacters through a common commutative group
scheme, when the centralizer of the second is contained in that of the first. -/
private theorem isIso_of_common_commutativeGroup
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)
    (ν ξ : cocharacterLattice T)
    (hZ : centralizer (CommGroupScheme.groupHom ξ ≫ i) ≤
      centralizer (CommGroupScheme.groupHom ν ≫ i)) :
    let χ := CommGroupScheme.groupHom ν ≫ i
    let ψ := CommGroupScheme.groupHom ξ ≫ i
    let ψminus := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ ψ
    IsIso (multiplication (Affine.unipotentHom χ)
      (Affine.unipotentHom ψminus) (Affine.unipotentHom ψ)) := by
  dsimp only
  let χ := CommGroupScheme.groupHom ν ≫ i
  let ψ := CommGroupScheme.groupHom ξ ≫ i
  let inversion := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1))
  let ψminus := inversion ≫ ψ
  let u := Affine.unipotentHom χ
  let a := Affine.unipotentHom ψminus
  let b := Affine.unipotentHom ψ
  let p := Affine.parabolicHom ψ
  let m := SubgroupFunctor.cellMultiplication a p
  have hu := Affine.isRepresentedBy_unipotentHom χ
  have ha := Affine.isRepresentedBy_unipotentHom ψminus
  have hb := Affine.isRepresentedBy_unipotentHom ψ
  have hp := Affine.isRepresentedBy_parabolicHom ψ
  have hm : IsOpenImmersion m.left := oppositeCellStatement k G ψ _ _ a p ha hp
  have hna : (unipotent ψminus).IsNormalizedBy (SubgroupFunctor.range χ) := by
    simpa only [ψminus, ψ, Category.assoc] using
      unipotent_isNormalizedBy_range_of_common_commutativeGroup i
        (CommGroupScheme.groupHom ν) (inversion ≫ CommGroupScheme.groupHom ξ)
  have hnp : (parabolic ψ).IsNormalizedBy (SubgroupFunctor.range χ) :=
    parabolic_isNormalizedBy_range_of_common_commutativeGroup i
      (CommGroupScheme.groupHom ν) (CommGroupScheme.groupHom ξ)
  have hstable : IsCocharacterStable χ m := by
    apply isCocharacterStable_product χ a p
    · rwa [ha.2]
    · rwa [hp.2]
  have hinj : HasInjectiveOppositeCellMultiplication i ξ :=
    hasInjectiveOppositeCellMultiplication_of_isAffine i ξ
  have hleft : (unipotent χ ⊓ unipotent ψminus).IsRepresentedBy
      (subgroupIntersectionHom u a) := by
    rw [← hu.2, ← ha.2]
    exact isRepresentedBy_subgroupIntersectionHom (Affine.isClosedSubgroup_unipotentHom χ)
      (Affine.isClosedSubgroup_unipotentHom ψminus)
  have hright : (unipotent χ ⊓ unipotent ψ).IsRepresentedBy
      (subgroupIntersectionHom u b) := by
    rw [← hu.2, ← hb.2]
    exact isRepresentedBy_subgroupIntersectionHom (Affine.isClosedSubgroup_unipotentHom χ)
      (Affine.isClosedSubgroup_unipotentHom ψ)
  change IsIso (multiplication u a b)
  apply isIso_of_yoneda_map_bijective
  intro X
  let L := subgroupIntersection u a
  let R := subgroupIntersection u b
  let coords (z : X ⟶ L.X ⊗ R.X) : (unipotent ψminus).carrier X × (parabolic ψ).carrier X :=
    (⟨_, (hleft.pointsEquiv X (z ≫ fst L.X R.X)).property.2⟩,
      ⟨_, unipotent_le_parabolic ψ X (hright.pointsEquiv X (z ≫ snd L.X R.X)).property.2⟩)
  constructor
  · intro z z' hz
    change z ≫ multiplication u a b = z' ≫ multiplication u a b at hz
    have h := congrArg (fun t : X ⟶ (Affine.unipotentScheme χ).X => t ≫ u.hom.hom) hz
    have h' : (coords z).1.val * (coords z).2.val =
        (coords z').1.val * (coords z').2.val := by
      change ((z ≫ fst L.X R.X) ≫ (subgroupIntersectionHom u a).hom.hom) *
          ((z ≫ snd L.X R.X) ≫ (subgroupIntersectionHom u b).hom.hom) =
        ((z' ≫ fst L.X R.X) ≫ (subgroupIntersectionHom u a).hom.hom) *
          ((z' ≫ snd L.X R.X) ≫ (subgroupIntersectionHom u b).hom.hom)
      simpa only [Category.assoc, comp_multiplication] using h
    have heq : coords z = coords z' := @hinj X (coords z) (coords z') h'
    let : Mono (subgroupIntersectionHom u a).hom.hom := hleft.1
    let : Mono (subgroupIntersectionHom u b).hom.hom := hright.1
    apply CartesianMonoidalCategory.hom_ext
    · apply (cancel_mono (subgroupIntersectionHom u a).hom.hom).mp
      exact congrArg (fun v => v.1.val) heq
    · apply (cancel_mono (subgroupIntersectionHom u b).hom.hom).mp
      exact congrArg (fun v => v.2.val) heq
  · intro z
    change ∃ x, x ≫ multiplication u a b = z
    let g := z ≫ u.hom.hom
    obtain ⟨e, he, he0⟩ := (hu.pointsEquiv X z).property
    have h0 : ∃ z₀ : X ⟶ (Affine.unipotentScheme ψminus).X ⊗ (Affine.parabolicScheme ψ).X,
        z₀ ≫ m = evalZero e := by
      refine ⟨lift 1 1, ?_⟩
      dsimp only [m]
      rw [he0, SubgroupFunctor.lift_cellMultiplication, MonObj.one_comp, MonObj.one_comp, one_mul]
    obtain ⟨l, hl⟩ := he.exists_lift_of_cocharacterStable χ m hstable h0
    have hC : HasProductContraction χ (unipotent ψminus) (parabolic ψ) g :=
      hasProductContraction_of_represented_lift χ _ _ ha hp he he0 l hl
    obtain ⟨x, y, hx, hy, hxχ, hyχ, hxy⟩ := hC.exists_unipotent_factors χ _ _ hna hnp hinj
    have hyψ : y ∈ (unipotent ψ).carrier X :=
      mem_unipotent_of_mem_unipotent_of_mem_parabolic χ ψ hZ hyχ hy
    let x' := (hleft.pointsEquiv X).symm ⟨x, hxχ, hx⟩
    let y' := (hright.pointsEquiv X).symm ⟨y, hyχ, hyψ⟩
    have hx' : x' ≫ (subgroupIntersectionHom u a).hom.hom = x :=
      hleft.pointsEquiv_symm_comp _
    have hy' : y' ≫ (subgroupIntersectionHom u b).hom.hom = y :=
      hright.pointsEquiv_symm_comp _
    have hfst : lift x' y' ≫ fst L.X R.X ≫ (subgroupIntersectionHom u a).hom.hom = x := by
      rw [lift_fst_assoc]
      exact hx'
    have hsnd : lift x' y' ≫ snd L.X R.X ≫ (subgroupIntersectionHom u b).hom.hom = y := by
      rw [lift_snd_assoc]
      exact hy'
    let : Mono u.hom.hom := hu.1
    refine ⟨lift x' y', (cancel_mono u.hom.hom).mp ?_⟩
    calc
      (lift x' y' ≫ multiplication u a b) ≫ u.hom.hom =
          (lift x' y' ≫ fst L.X R.X ≫ (subgroupIntersectionHom u a).hom.hom) *
            (lift x' y' ≫ snd L.X R.X ≫ (subgroupIntersectionHom u b).hom.hom) :=
        (Category.assoc _ _ _).trans (comp_multiplication u a b (lift x' y'))
      _ = x * y := congrArg₂ (· * ·) hfst hsnd
      _ = g := hxy.symm

end BruhatFactorization

set_option maxHeartbeats 600000 in
/-- The unipotent factors of a rational Bruhat cell multiply isomorphically
onto the dynamic unipotent subgroup, over all test schemes. -/
theorem rationalBruhatFactorization : RationalBruhatFactorizationStatement.{u} := by
  intro k _ G hG T i hi ν
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  dsimp only
  intro hν n
  let χ := CommGroupScheme.groupHom ν ≫ i
  let ψ := χ ≫ (G.innerIso n.val).hom
  let ξ := cocharacterAut (normalizingAut i n) ν
  have hξ : CommGroupScheme.groupHom ξ ≫ i = ψ := groupHom_cocharacterAut_comp i n ν
  have hZ := genericCentralizer k G hG T i hi ν hν
  have hψχ : Dynamic.centralizer (CommGroupScheme.groupHom ξ ≫ i) ≤ Dynamic.centralizer χ := by
    rw [hξ, centralizer_conjugate_eq_torusCentralizer i χ hZ n, hZ]
  change IsIso (BruhatFactorization.multiplication (Dynamic.Affine.unipotentHom χ)
    (Dynamic.Affine.unipotentHom
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ ψ))
    (Dynamic.Affine.unipotentHom ψ))
  rw [← hξ]
  exact BruhatFactorization.isIso_of_common_commutativeGroup i ν ξ hψχ

end Langlands.GroupScheme
