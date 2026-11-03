import Langlands.GroupScheme.Rational.TorusActionBridge
import Langlands.GroupScheme.Rational.TorusWeightTangent
import Langlands.GroupScheme.Rational.PointedCoordinateDecompositionProof
import Langlands.GroupScheme.Lie.AffineModule

/-! # Lie weights of a split-torus action through a corepresented model -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeRoot

open Corepresented
open GeneralLinear.DualNumber (coefficientAlgMap epsilonScaleAlg)

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}} {B : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B) (ψ : groupScheme F e ≅ G)
  {I : Type u} [Fintype I] [DecidableEq I]

/-! ### Coordinates of points through the model -/

/-- The coordinates in the corepresented model of the points of `G` over an algebra. -/
def lieCoords (A : Type u) [CommRing A] [Algebra k A] :
    Lie.AffinePoints G A ≃* F.obj (CommAlgCat.of (CommRingCat.of k) A) :=
  (isoPointsEquiv ψ.symm _).trans (affinePointsEquiv F e _)

theorem lieCoords_apply {A : Type u} [CommRing A] [Algebra k A] (g : Lie.AffinePoints G A) :
    lieCoords e ψ A g = affinePointsEquiv F e _ (g ≫ ψ.inv.hom.hom) :=
  rfl

/-- Coordinates commute with change of algebra. -/
theorem lieCoords_affineMap {A A' : Type u} [CommRing A] [Algebra k A] [CommRing A']
    [Algebra k A'] (f : A →ₐ[k] A') (g : Lie.AffinePoints G A) :
    lieCoords e ψ A' (Lie.affineMap G f g) = F.map (CommAlgCat.ofHom f) (lieCoords e ψ A g) := by
  rw [lieCoords_apply, lieCoords_apply, Lie.affineMap_apply, Category.assoc]
  exact affinePointsEquiv_naturality F e (CommAlgCat.ofHom f) _

/-- The coordinates of a dual-number identity-kernel point reduce to the identity. -/
theorem lieCoords_reduction (X : lieKernel G k) :
    F.map (dualReduction (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k)))
      (lieCoords e ψ (DualNumber k) X.val) = 1 := by
  have h := lieCoords_affineMap e ψ (TrivSqZeroExt.fstHom (CommRingCat.of k) k k) X.val
  have hX : Lie.affineMap G (TrivSqZeroExt.fstHom (CommRingCat.of k) k k) X.val = 1 := X.property
  rw [hX, map_one] at h
  exact h.symm

variable (φ : S.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I) (b : AutomorphicAction S.toGrp G)

omit [DecidableEq I] in
/-- The action of `b` on points of `G`, in coordinates. -/
theorem lieCoords_act {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A)
    (g : Lie.AffinePoints G A) :
    lieCoords e ψ A (b.act s g) = (TorusAction.ofAutomorphicAction e (b.transport φ.inv ψ)).act
      (splitTorus.algebraPointsEquiv I A (s ≫ φ.hom.hom.hom)) (lieCoords e ψ A g) := by
  rw [lieCoords_apply, lieCoords_apply, AutomorphicAction.act_eq_transport b ψ φ, Category.assoc,
    iso_hom_inv_hom, Category.comp_id]
  exact affinePointsEquiv_act e (b.transport φ.inv ψ) (s ≫ φ.hom.hom.hom) (g ≫ ψ.inv.hom.hom)

omit [DecidableEq I] in
/-- The unit coordinates of a constant dual-number point. -/
theorem algebraPointsEquiv_constant {A : Type u} [CommRing A] [Algebra k A]
    (s : Lie.AffinePoints S.toGrp A) :
    splitTorus.algebraPointsEquiv I (DualNumber A) (Lie.constant S.toGrp s ≫ φ.hom.hom.hom) =
      fun i => Units.map (TrivSqZeroExt.inlAlgHom (CommRingCat.of k) A A).toMonoidHom
        (splitTorus.algebraPointsEquiv I A (s ≫ φ.hom.hom.hom) i) := by
  have h : Lie.constant S.toGrp s ≫ φ.hom.hom.hom =
      Lie.affineMap _ (TrivSqZeroExt.inlAlgHom (CommRingCat.of k) A A) (s ≫ φ.hom.hom.hom) := by
    rw [Lie.constant, Lie.affineMap_apply, Lie.affineMap_apply, Category.assoc]
  rw [h, splitTorus.algebraPointsEquiv_naturality]

omit [DecidableEq I] in
/-- The exponent vector of a character gives back the character. -/
theorem characterEquiv_characterExponents (χ : characterLattice S) :
    PointedCoordinateWeights.characterEquiv φ (characterExponents φ χ) = χ := by
  apply (PointedCoordinateWeights.characterEquiv φ).symm.injective
  rw [AddEquiv.symm_apply_apply]
  rfl

/-- A character's value on a point is the monomial in the unit coordinates with the
character's exponent vector. -/
theorem characterValue_eq_exponentValue {A : Type u} [CommRing A] [Algebra k A]
    (χ : characterLattice S) (s : Lie.AffinePoints S.toGrp A) :
    Lie.characterValue χ s = splitTorus.exponentValue I
      (splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I A (s ≫ φ.hom.hom.hom))
      (Multiplicative.ofAdd (characterExponents φ χ)) := by
  conv_lhs => rw [← characterEquiv_characterExponents φ χ]
  exact PointedCoordinateWeights.characterValue_eq_pointCharacter φ s _

/-! ### Eigenvectors and weight tangent vectors -/

variable [IsAffineHom G.X.hom]

omit [IsAffineHom G.X.hom] in
/-- A dual-number tangent vector is an eigenvector of weight `χ` for `b` exactly when its
coordinates form a weight tangent vector of weight `characterExponents φ χ`. -/
theorem mem_actionEigenvectors_iff (χ : characterLattice S) (X : Additive (lieKernel G k)) :
    X ∈ actionEigenvectors b χ ↔ IsWeightTangent (TorusAction.ofAutomorphicAction e (b.transport φ.inv ψ))
      (characterExponents φ χ) (lieCoords e ψ (DualNumber k) X.toMul.val) := by
  constructor
  · intro hX A t
    let s : Lie.AffinePoints S.toGrp A :=
      (splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I A).symm t ≫ φ.inv.hom.hom
    have ht : splitTorus.algebraPointsEquiv I A (s ≫ φ.hom.hom.hom) = t := by
      change splitTorus.algebraPointsEquiv I A
        (((splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I A).symm t ≫ φ.inv.hom.hom) ≫
          φ.hom.hom.hom) = t
      rw [Category.assoc, iso_inv_hom_hom, Category.comp_id, MulEquiv.apply_symm_apply]
    have h := congrArg (lieCoords e ψ (DualNumber A)) (hX A s)
    rw [lieCoords_act e ψ φ b, lieKernelScale_val, lieCoords_affineMap, lieKernelMap_val,
      lieCoords_affineMap, characterValue_eq_exponentValue φ, algebraPointsEquiv_constant, ht] at h
    exact h
  · intro hX A _ _ s
    apply (lieCoords e ψ (DualNumber A)).injective
    rw [lieCoords_act e ψ φ b, lieKernelScale_val, lieCoords_affineMap, lieKernelMap_val,
      lieCoords_affineMap, characterValue_eq_exponentValue φ, algebraPointsEquiv_constant]
    exact hX (CommAlgCat.of (CommRingCat.of k) A) _

/-! ### Weight supports of transported weight subgroups -/

/-- On affine tests, membership in a cut-out subgroup functor is membership of the coordinates. -/
theorem mem_cutSubgroupFunctor_affine {H : ∀ A : CommAlgCat.{u} (CommRingCat.of k),
      Subgroup (F.obj A)} {J : Ideal B} (hJ : IsCutOutBy e H J) {A : CommAlgCat.{u} (CommRingCat.of k)}
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ (groupScheme F e).X) :
    x ∈ (cutSubgroupFunctor hJ).carrier ((algSpec (CommRingCat.of k)).obj (op A)) ↔
      affinePointsEquiv F e A x ∈ H A := by
  rw [mem_cutSubgroupFunctor]
  constructor
  · intro h
    have h' := hJ.map_mem (affineSectionsIso A).hom h
    rwa [map_affineSectionsIso_pointsEquiv] at h'
  · intro h
    rw [pointsEquiv_eq_affinePointsEquiv]
    exact hJ.map_mem _ h

/-- The tangent vectors whose infinitesimal coordinates are supported on one weight form a
submodule. -/
def sndSupportSubmodule (σ : TorusAction F I) (χ : I → ℤ) :
    Submodule k (Additive (lieKernel G k)) where
  carrier := {X | ∀ f m, m ≠ χ → (coord e (lieCoords e ψ (DualNumber k) X.toMul.val)
    (comp e σ m f)).snd = 0}
  add_mem' {X Y} hX hY f m hm := by
    change (coord e (lieCoords e ψ (DualNumber k) (X.toMul.val * Y.toMul.val))
      (comp e σ m f)).snd = 0
    rw [map_mul, snd_coord_mul e (lieCoords_reduction e ψ X.toMul)
      (lieCoords_reduction e ψ Y.toMul), hX f m hm, hY f m hm, add_zero]
  zero_mem' f m _ := by
    change (coord e (lieCoords e ψ (DualNumber k) 1) (comp e σ m f)).snd = 0
    rw [map_one, coord_one, AlgHom.comp_apply, Algebra.ofId_apply,
      TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_inl]
  smul_mem' c X hX f m hm := by
    change (coord e (lieCoords e ψ (DualNumber k)
      (Lie.affineMap G (epsilonScaleAlg (R := CommRingCat.of k) c) X.toMul.val))
        (comp e σ m f)).snd = 0
    rw [lieCoords_affineMap, coord_map, AlgHom.comp_apply]
    change (epsilonScaleAlg (R := CommRingCat.of k) c _).snd = 0
    rw [epsilonScaleAlg_snd, hX f m hm, mul_zero]

/-- The weight space of `χ` consists of tangent vectors whose infinitesimal coordinates are
supported on `characterExponents φ χ`. -/
theorem actionWeightSpace_le_sndSupportSubmodule (χ : characterLattice S) :
    actionWeightSpace b χ ≤
      sndSupportSubmodule e ψ (TorusAction.ofAutomorphicAction e (b.transport φ.inv ψ)) (characterExponents φ χ) := by
  refine Submodule.span_le.2 fun X hX f m hm => ?_
  exact snd_comp_eq_zero_of_isWeightTangent e _
    ((mem_actionEigenvectors_iff e ψ φ b χ X).1 hX) f hm

/-- The weights in the tangent space of the weight subgroup of `P`, transported to `G`, are the
characters whose exponent vectors lie in `P`. -/
theorem actionWeightSupport_comap_weightSubgroup_subset (P : AddSubsemigroup (I → ℤ)) :
    actionWeightSupport b ((cutSubgroupFunctor (isCutOutBy_weightIdeal e
      (TorusAction.ofAutomorphicAction e (b.transport φ.inv ψ)) P)).comap ψ.inv) ⊆
        {χ | characterExponents φ χ ∈ P} := by
  rintro χ ⟨X, hX0, hXW, hXU⟩
  by_contra hχ
  rw [SubgroupFunctor.mem_comap, mem_cutSubgroupFunctor_affine] at hXU
  have hD := actionWeightSpace_le_sndSupportSubmodule e ψ φ b χ hXW
  have h1 : lieCoords e ψ (DualNumber k) X.toMul.val = 1 :=
    eq_one_of_mem_weightSubgroup_of_snd_comp e _ P hχ (lieCoords_reduction e ψ X.toMul) hXU hD
  apply hX0
  change Additive.ofMul X.toMul = Additive.ofMul 1
  congr 1
  apply Subtype.ext
  exact (lieCoords e ψ (DualNumber k)).injective (h1.trans (map_one _).symm)

/-! ### Rigidity of tangent vectors of subgroups with small weight support -/

omit [IsAffineHom G.X.hom] in
/-- The coordinates of a dual-number point of `G` lie in the affine subgroups of the pullback of
a subgroup functor exactly when the point lies in the subgroup functor. -/
theorem lieCoords_mem_affineSubgroups_iff {F' : SubgroupFunctor G}
    (g : Lie.AffinePoints G (DualNumber k)) :
    lieCoords e ψ (DualNumber k) g ∈
        affineSubgroups (F'.comap ψ.hom) (CommAlgCat.of (CommRingCat.of k) (DualNumber k)) ↔
      g ∈ F'.carrier ((algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of (CommRingCat.of k) (DualNumber k)))) := by
  change (affinePointsEquiv F e _).symm (affinePointsEquiv F e _ (g ≫ ψ.inv.hom.hom)) ∈
    (F'.comap ψ.hom).carrier _ ↔ _
  rw [MulEquiv.symm_apply_apply, SubgroupFunctor.mem_comap, Category.assoc, iso_inv_hom_hom,
    Category.comp_id]

/-- Tangent rigidity outside `P` for a subgroup functor `F'` of `G` whose tangent weights have
exponent vectors in `P`: for an ideal `J` cutting out the pullback of `F'` to the model, stable
under the induced torus action, every tangent vector of the cut-out group whose infinitesimal
coordinates are supported on one exponent vector outside `P` is trivial. This is the rigidity
hypothesis of `Corepresented.le_weightSubgroup`. -/
theorem tangentRigid_of_actionWeightSupport_subset (P : AddSubsemigroup (I → ℤ))
    {F' : SubgroupFunctor G} (hF' : actionWeightSupport b F' ⊆ {χ | characterExponents φ χ ∈ P})
    {J : Ideal B} (hJ : IsCutOutBy e (affineSubgroups (F'.comap ψ.hom)) J)
    (hH : ∀ {A : CommAlgCat.{u} (CommRingCat.of k)} (t : I → Aˣ) {x : F.obj A},
      x ∈ affineSubgroups (F'.comap ψ.hom) A →
        (TorusAction.ofAutomorphicAction e (b.transport φ.inv ψ)).act t x ∈
          affineSubgroups (F'.comap ψ.hom) A) :
    ∀ χ ∉ P, ∀ X : (cutFunctor hJ).obj
        (CommAlgCat.of (CommRingCat.of k) (DualNumber (CommRingCat.of k))),
      (cutFunctor hJ).map
          (dualReduction (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k))) X = 1 →
        (∀ g m, m ≠ χ → (coord (cutCorepresentableBy hJ) X (comp (cutCorepresentableBy hJ)
          ((TorusAction.ofAutomorphicAction e (b.transport φ.inv ψ)).restrict hJ hH) m g)).snd =
            0) → X = 1 := by
  intro χ' hχ' X hX hD
  set σ := TorusAction.ofAutomorphicAction e (b.transport φ.inv ψ)
  have hx1 : F.map (dualReduction (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k))) X.1 = 1 :=
    congrArg Subtype.val hX
  have hDx : ∀ f m, m ≠ χ' → (coord e X.1 (comp e σ m f)).snd = 0 := by
    intro f m hm
    have h := hD (Ideal.Quotient.mk J f) m hm
    rwa [comp_restrict, coord_cut_mk] at h
  have hW : IsWeightTangent σ χ' X.1 := isWeightTangent_of_snd_comp e σ hx1 hDx
  let y : Lie.AffinePoints G (DualNumber k) := (lieCoords e ψ (DualNumber k)).symm X.1
  have hyc : lieCoords e ψ (DualNumber k) y = X.1 := MulEquiv.apply_symm_apply _ _
  have hy : y ∈ lieKernel G k := by
    change Lie.affineMap G (TrivSqZeroExt.fstHom (CommRingCat.of k) k k) y = 1
    apply (lieCoords e ψ k).injective
    rw [lieCoords_affineMap, hyc, map_one]
    exact hx1
  let Y : lieKernel G k := ⟨y, hy⟩
  have hEig : Additive.ofMul Y ∈ actionEigenvectors b ((characterExponents φ).symm χ') := by
    rw [mem_actionEigenvectors_iff e ψ φ b, AddEquiv.apply_symm_apply]
    change IsWeightTangent σ χ' (lieCoords e ψ (DualNumber k) y)
    rw [hyc]
    exact hW
  by_contra hne
  have hY0 : Additive.ofMul Y ≠ 0 := by
    intro h0
    apply hne
    apply Subtype.ext
    have hY1 : y = 1 := congrArg Subtype.val (congrArg Additive.toMul h0)
    rw [← hyc, hY1, map_one]
    rfl
  have hYF : y ∈ F'.carrier ((algSpec (CommRingCat.of k)).obj
      (op (CommAlgCat.of (CommRingCat.of k) (DualNumber k)))) := by
    rw [← lieCoords_mem_affineSubgroups_iff e ψ, hyc]
    exact X.2
  have hmem : (characterExponents φ).symm χ' ∈ actionWeightSupport b F' :=
    ⟨Additive.ofMul Y, hY0, Submodule.subset_span hEig, hYF⟩
  have h := hF' hmem
  change characterExponents φ ((characterExponents φ).symm χ') ∈ P at h
  rw [AddEquiv.apply_symm_apply] at h
  exact hχ' h

end RelativeRoot

end Langlands.GroupScheme
