import Langlands.GroupScheme.Rational.TorusWeightSubgroups
import Langlands.GroupScheme.RepresentedAction
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.AffineCorepresented
import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.CorepresentedSmooth
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Rational.WeightSemigroup
import Langlands.GroupScheme.Torus.WeightDecomposition

/-! # Torus actions on algebra points from automorphic actions of split tori -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-! ### Transport along isomorphisms -/

section Transport

variable {S : Scheme.{u}} {H G H' G' K : GroupScheme S}

theorem iso_hom_inv_hom (ψ : G' ≅ G) : ψ.hom.hom.hom ≫ ψ.inv.hom.hom = 𝟙 G'.X :=
  congrArg (fun f => f.hom.hom) ψ.hom_inv_id

theorem iso_inv_hom_hom (ψ : G' ≅ G) : ψ.inv.hom.hom ≫ ψ.hom.hom.hom = 𝟙 G.X :=
  congrArg (fun f => f.hom.hom) ψ.inv_hom_id

namespace AutomorphicAction

variable (b : AutomorphicAction H G) (φ : H' ⟶ H) (ψ : G' ≅ G)

theorem lift_comp_transportHom {T : Over S} (h : T ⟶ H'.X) (g : T ⟶ G'.X) :
    lift h g ≫ (φ.hom.hom ⊗ₘ ψ.hom.hom.hom) ≫ b.hom ≫ ψ.inv.hom.hom =
      b.act (h ≫ φ.hom.hom) (g ≫ ψ.hom.hom.hom) ≫ ψ.inv.hom.hom := by
  rw [← Category.assoc, lift_map, act_eq, Category.assoc]

/-- An action transported along a homomorphism of acting groups and an isomorphism of the
groups acted on. -/
def transport : AutomorphicAction H' G' where
  hom := (φ.hom.hom ⊗ₘ ψ.hom.hom.hom) ≫ b.hom ≫ ψ.inv.hom.hom
  one_left g := by
    rw [lift_comp_transportHom, MonObj.one_comp, act_one_left, Category.assoc, iso_hom_inv_hom,
      Category.comp_id]
  mul_left h h' g := by
    simp only [lift_comp_transportHom, MonObj.mul_comp, act_mul_left, Category.assoc,
      iso_inv_hom_hom, Category.comp_id]
  mul_right h g g' := by
    simp only [lift_comp_transportHom, MonObj.mul_comp, act_mul_right]

theorem transport_act {T : Over S} (h : T ⟶ H'.X) (g : T ⟶ G'.X) :
    (b.transport φ ψ).act h g = b.act (h ≫ φ.hom.hom) (g ≫ ψ.hom.hom.hom) ≫ ψ.inv.hom.hom :=
  lift_comp_transportHom b φ ψ h g

/-- The original action is recovered from the transported one. -/
theorem act_eq_transport (φ : H ≅ H') {T : Over S} (h : T ⟶ H.X) (g : T ⟶ G.X) :
    b.act h g = (b.transport φ.inv ψ).act (h ≫ φ.hom.hom.hom) (g ≫ ψ.inv.hom.hom) ≫
      ψ.hom.hom.hom := by
  simp only [transport_act, Category.assoc, iso_hom_inv_hom, iso_inv_hom_hom, Category.comp_id]

end AutomorphicAction

/-- Stability transfers from the transported action to the preimage of the subgroup functor
under the inverse isomorphism. -/
theorem AutomorphicAction.isStable_transport (b : AutomorphicAction H G) (φ : H ≅ H')
    (ψ : G' ≅ G) {U : SubgroupFunctor G'} (hU : (b.transport φ.inv ψ).IsStable U) :
    b.IsStable (U.comap ψ.inv) := by
  intro T h g hg
  rw [SubgroupFunctor.mem_comap] at hg ⊢
  rw [AutomorphicAction.act_eq_transport b ψ φ, Category.assoc, iso_hom_inv_hom,
    Category.comp_id]
  exact hU T _ _ hg

end Transport

namespace Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B) {I : Type u} [Finite I]

/-- Points on a test scheme factor through its relative affinization, and the factor has
the same coordinates. -/
theorem pointsEquiv_unit_comp (T : Over (Spec R))
    (y : (algSpec R).obj ((algΓ R).obj T) ⟶ (groupScheme F e).X) :
    pointsEquiv F e T ((algΓAlgSpecAdjunction R).unit.app T ≫ y) =
      affinePointsEquiv F e ((algΓ R).obj T).unop y := by
  obtain ⟨f, rfl⟩ : ∃ f : B ⟶ ((algΓ R).obj T).unop, (algSpec R).map f.op = y :=
    ⟨(algSpec.fullyFaithful.preimage y).unop, algSpec.fullyFaithful.map_preimage y⟩
  have h : ((algΓAlgSpecAdjunction R).homEquiv T (op B)).symm
      ((algΓAlgSpecAdjunction R).unit.app T ≫ (algSpec R).map f.op) = f.op := by
    rw [← Adjunction.homEquiv_unit, Equiv.symm_apply_apply]
  rw [affinePointsEquiv_map]
  exact congrArg (fun g => e.homEquiv g.unop) h

/-- The factor of a point through the relative affinization of its test scheme. -/
def affineFactor {T : Over (Spec R)} (x : T ⟶ (groupScheme F e).X) :
    (algSpec R).obj ((algΓ R).obj T) ⟶ (groupScheme F e).X :=
  (algSpec R).map (((algΓAlgSpecAdjunction R).homEquiv T (op B)).symm x)

/-- Every point on a test scheme factors through the relative affinization unit. -/
@[simp] theorem unit_comp_affineFactor {T : Over (Spec R)} (x : T ⟶ (groupScheme F e).X) :
    (algΓAlgSpecAdjunction R).unit.app T ≫ affineFactor e x = x :=
  ((algΓAlgSpecAdjunction R).homEquiv_unit T (op B) _).symm.trans (Equiv.apply_symm_apply _ x)

variable (I) in
/-- The split-torus point over an algebra with prescribed unit coordinates. -/
abbrev torusPt (A : CommAlgCat.{u} R) (t : I → Aˣ) :
    Lie.AffinePoints (splitTorus (Spec R) I) A :=
  (splitTorus.algebraPointsEquiv I A).symm t

theorem torusPt_naturality {A A' : CommAlgCat.{u} R} (g : A ⟶ A') (t : I → Aˣ) :
    (algSpec R).map g.op ≫ torusPt I A t =
      torusPt I A' (fun i => Units.map g.hom.toMonoidHom (t i)) := by
  apply (splitTorus.algebraPointsEquiv I A').injective
  have h := splitTorus.algebraPointsEquiv_naturality I g.hom (torusPt I A t)
  rw [MulEquiv.apply_symm_apply] at h ⊢
  exact h

/-- The action of unit coordinates on algebra points induced by an automorphic action of
the split torus on the corepresented group scheme. -/
def TorusAction.ofAutomorphicAction
    (b : AutomorphicAction (splitTorus (Spec R) I) (groupScheme F e)) : TorusAction F I where
  act {A} t x := affinePointsEquiv F e A (b.act (torusPt I A t) ((affinePointsEquiv F e A).symm x))
  act_one {A} x := by
    simp only [torusPt, map_one, AutomorphicAction.act_one_left, MulEquiv.apply_symm_apply]
  act_mul {A} t t' x := by
    simp only [torusPt, map_mul, AutomorphicAction.act_mul_left, MulEquiv.symm_apply_apply]
  act_map_mul {A} t x y := by
    simp only [map_mul, AutomorphicAction.act_mul_right]
  naturality {A A'} g t x := by
    rw [← affinePointsEquiv_naturality, AutomorphicAction.naturality, torusPt_naturality]
    congr 3
    apply (affinePointsEquiv F e A').injective
    rw [affinePointsEquiv_naturality, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

variable (b : AutomorphicAction (splitTorus (Spec R) I) (groupScheme F e))

/-- On affine tests the automorphic action is the coordinate action of the unit coordinates. -/
theorem affinePointsEquiv_act {A : CommAlgCat.{u} R}
    (s : (algSpec R).obj (op A) ⟶ (splitTorus (Spec R) I).X)
    (x : (algSpec R).obj (op A) ⟶ (groupScheme F e).X) :
    affinePointsEquiv F e A (b.act s x) =
      (TorusAction.ofAutomorphicAction e b).act (splitTorus.algebraPointsEquiv I A s)
        (affinePointsEquiv F e A x) := by
  change _ = affinePointsEquiv F e A (b.act
    ((splitTorus.algebraPointsEquiv I A).symm (splitTorus.algebraPointsEquiv I A s))
    ((affinePointsEquiv F e A).symm (affinePointsEquiv F e A x)))
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

/-- On every test scheme the automorphic action is a coordinate action of some units of the
relative global sections. -/
theorem exists_pointsEquiv_act (T : Over (Spec R)) (s : T ⟶ (splitTorus (Spec R) I).X)
    (x : T ⟶ (groupScheme F e).X) :
    ∃ t : I → (((algΓ R).obj T).unop)ˣ,
      pointsEquiv F e T (b.act s x) =
        (TorusAction.ofAutomorphicAction e b).act t (pointsEquiv F e T x) := by
  have : IsAffineHom (splitTorus (Spec R) I).X.hom := isAffineHom_splitTorus_spec R I
  refine ⟨splitTorus.algebraPointsEquiv I _ (Lie.affinizationFactor (splitTorus (Spec R) I) s), ?_⟩
  conv_lhs => rw [← Lie.unit_affinizationFactor (splitTorus (Spec R) I) s,
    ← unit_comp_affineFactor e x, ← AutomorphicAction.naturality, pointsEquiv_unit_comp,
    affinePointsEquiv_act]
  conv_rhs => rw [← unit_comp_affineFactor e x, pointsEquiv_unit_comp]
  rfl

/-- A family cut out by an ideal and stable under the induced torus action gives a subgroup
functor stable under the automorphic action. -/
theorem isStable_cutSubgroupFunctor {H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)} {J : Ideal B}
    (hI : IsCutOutBy e H J)
    (hH : ∀ {A : CommAlgCat.{u} R} (t : I → Aˣ) {x : F.obj A}, x ∈ H A →
      (TorusAction.ofAutomorphicAction e b).act t x ∈ H A) :
    b.IsStable (cutSubgroupFunctor hI) := by
  intro T s x hx
  obtain ⟨t, ht⟩ := exists_pointsEquiv_act e b T s x
  rw [mem_cutSubgroupFunctor, ht]
  exact hH t hx

/-- The subgroup functors cut out by weight conditions are stable under the action. -/
theorem isStable_weightSubgroup [Fintype I] [DecidableEq I] (P : AddSubsemigroup (I → ℤ)) :
    b.IsStable (cutSubgroupFunctor
      (isCutOutBy_weightIdeal e (TorusAction.ofAutomorphicAction e b) P)) :=
  isStable_cutSubgroupFunctor e b _ fun {_} t {_} hx => act_mem_weightSubgroup e _ P t hx

end Corepresented

/-! ### Smoothness and finite type of the coordinate algebra -/

namespace AffineCoordinates

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffine G.X.left]

/-- The coordinate algebra of a smooth affine group scheme is formally smooth. -/
theorem formallySmooth_algebra (hG : Smooth G.X.hom) : Algebra.FormallySmooth R (algebra G) :=
  have := smooth_algebra G hG
  inferInstance

/-- The coordinate algebra of a smooth affine group scheme is of finite type. -/
theorem finiteType_algebra (hG : Smooth G.X.hom) : Algebra.FiniteType R (algebra G) :=
  have := smooth_algebra G hG
  inferInstance

end AffineCoordinates

/-! ### Smooth connected cut subgroups with polynomial coordinates -/

namespace Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  {e : (F ⋙ forget GrpCat).CorepresentableBy B} {H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)}
  {J : Ideal B} (hJ : IsCutOutBy e H J) {κ : Type*} [Finite κ] {x : κ → B ⧸ J}

/-- A cut-out subgroup scheme whose coordinate algebra is a polynomial algebra in finitely many
variables is smooth. -/
theorem smooth_cutGroupScheme_of_bijective (hx : Function.Bijective (MvPolynomial.aeval (R := R) x)) :
    Smooth (cutGroupScheme hJ).X.hom := by
  rw [smooth_groupScheme_iff]
  have : Algebra.Smooth R (MvPolynomial κ R) := {}
  exact Algebra.Smooth.of_equiv (AlgEquiv.ofBijective _ hx)

omit [Finite κ] in
/-- Over a domain, a cut-out subgroup scheme whose coordinate algebra is a polynomial algebra
is connected. -/
theorem connectedSpace_cutGroupScheme [IsDomain R]
    (hx : Function.Bijective (MvPolynomial.aeval (R := R) x)) :
    ConnectedSpace (cutGroupScheme hJ).X.left := by
  have : IsDomain (B ⧸ J) :=
    MulEquiv.isDomain (MvPolynomial κ R) (AlgEquiv.ofBijective _ hx).symm.toMulEquiv
  change ConnectedSpace (Spec (CommRingCat.of (B ⧸ J)))
  infer_instance

end Corepresented

namespace RelativeRoot

variable {k : Type u} [Field k]

/-- Smooth connected closed subgroup functors are carried along an isomorphism of the ambient
group, as preimages under the inverse isomorphism. -/
theorem IsSmoothConnectedClosed.comap_iso {G G' : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom] {U : SubgroupFunctor G'}
    (hU : IsSmoothConnectedClosed U) (ψ : G' ≅ G) : IsSmoothConnectedClosed (U.comap ψ.inv) := by
  obtain ⟨K, j, hj, hjc, hKs, hKc⟩ := hU
  exact ⟨K, j ≫ ψ.hom, hj.comp_iso ψ, hjc.comp_iso ψ, hKs, hKc⟩

/-- A cut-out subgroup functor whose coordinate algebra is a polynomial algebra in finitely
many variables over a field is smooth, connected and closed. -/
theorem isSmoothConnectedClosed_cutSubgroupFunctor
    {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}} {B : CommAlgCat.{u} (CommRingCat.of k)}
    {e : (F ⋙ forget GrpCat).CorepresentableBy B}
    {H : ∀ A : CommAlgCat.{u} (CommRingCat.of k), Subgroup (F.obj A)} {J : Ideal B}
    (hJ : Corepresented.IsCutOutBy e H J) {κ : Type*} [Finite κ] {x : κ → B ⧸ J}
    (hx : Function.Bijective (MvPolynomial.aeval (R := k) x)) :
    IsSmoothConnectedClosed (Corepresented.cutSubgroupFunctor hJ) :=
  ⟨_, _, Corepresented.isRepresentedBy_cutHom hJ, Corepresented.isClosedSubgroup_cutHom hJ,
    Corepresented.smooth_cutGroupScheme_of_bijective hJ hx, Corepresented.connectedSpace_cutGroupScheme hJ hx⟩

end RelativeRoot

/-! ### Exponent vectors of characters of a split torus -/

section Characters

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))} {I : Type u}
  [Finite I] (φ : S.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I)

/-- The exponent vectors of the characters of a split torus, through a splitting. -/
def characterExponents : characterLattice S ≃+ (I → ℤ) :=
  (characterLattice.comapIso φ.symm).trans (splitTorus.characterLatticeEquiv k I)

/-- On points a character is the monomial in the unit coordinates with its exponent vector. -/
theorem pointsEquiv_characterExponents [Fintype I] (χ : characterLattice S)
    {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.X) :
    Gm.pointsEquiv _ T (s ≫ (CommGroupScheme.groupHom χ).hom.hom) =
      ∏ i, splitTorus.pointsEquiv I T (s ≫ φ.hom.hom.hom) i ^ characterExponents φ χ i := by
  have hχ : (splitTorus.characterLatticeEquiv k I).symm (characterExponents φ χ) =
      Additive.ofMul (φ.inv ≫ CommGroupScheme.groupHom χ) :=
    (splitTorus.characterLatticeEquiv k I).symm_apply_apply _
  rw [← splitTorus.pointsEquiv_characterLatticeEquiv_symm, hχ]
  congr 1
  change s ≫ _ = (s ≫ φ.hom.hom.hom) ≫ φ.inv.hom.hom ≫ (CommGroupScheme.groupHom χ).hom.hom
  rw [Category.assoc, ← Category.assoc φ.hom.hom.hom, iso_hom_inv_hom, Category.id_comp]

end Characters

end Langlands.GroupScheme
