import Langlands.GroupScheme.AutomorphicAction.Cocycles
import Langlands.GroupScheme.Torus.TwistedLifting
import Langlands.GroupScheme.Torus.AffineCharacterAction

/-! # Nilpotent lifting of conjugacies between diagonalizable cocycles

Let `a` be an actual action of `D(M)` on an affine group scheme `G` over `Spec R`, and let
`cx`, `cy` be actual cocycles over an affine test `Spec C`. The points `g` of `G` with
`conjugate g cx = cy` are the fixed points of the twisted character action
`t · g = cy(t) a_t(g) cx(t)⁻¹` on points of `G` over `C`-algebras. Applying the published
fixed-point lifting theorem after base change of the coordinate algebra to `C`, conjugacies
over `C ⧸ I` lift to conjugacies over `C` whenever `I` is nilpotent.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CharacterAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {G : GroupScheme (Spec R)} [IsAffine G.X.left] {C : CommAlgCat.{u} R}

section Coordinates

/-- The point of `G` over the restriction of scalars of a `C`-algebra given by a point of the
base change of the coordinate algebra. -/
def coordinatePoint {D : CommAlgCat.{u} (baseRing C)}
    (p : baseChange C (AffineCoordinates.algebra G) ⟶ D) :
    (algSpec R).obj (op (restrictScalars C D)) ⟶ G.X :=
  AffineCoordinates.pointEquiv G _ (baseChangeEquiv D p)

/-- The point of the base change with a prescribed point of `G`. -/
def ofCoordinatePoint {D : CommAlgCat.{u} (baseRing C)}
    (g : (algSpec R).obj (op (restrictScalars C D)) ⟶ G.X) :
    baseChange C (AffineCoordinates.algebra G) ⟶ D :=
  (baseChangeEquiv D).symm ((AffineCoordinates.pointEquiv G _).symm g)

@[simp] theorem coordinatePoint_ofCoordinatePoint {D : CommAlgCat.{u} (baseRing C)}
    (g : (algSpec R).obj (op (restrictScalars C D)) ⟶ G.X) :
    coordinatePoint (ofCoordinatePoint g) = g := by
  simp only [coordinatePoint, ofCoordinatePoint, Equiv.apply_symm_apply]

theorem coordinatePoint_injective {D : CommAlgCat.{u} (baseRing C)} :
    Function.Injective (coordinatePoint (G := G) (D := D)) :=
  (AffineCoordinates.pointEquiv G _).injective.comp (baseChangeEquiv D).injective

theorem coordinatePoint_comp {D D' : CommAlgCat.{u} (baseRing C)}
    (p : baseChange C (AffineCoordinates.algebra G) ⟶ D) (f : D ⟶ D') :
    coordinatePoint (p ≫ f) =
      (algSpec R).map (restrictScalarsMap f).op ≫ coordinatePoint p := by
  rw [coordinatePoint, baseChangeEquiv_comp, AffineCoordinates.pointEquiv_comp]
  rfl

/-- The structure morphism of a `C`-algebra, as a test morphism to `Spec C`. -/
abbrev structurePoint (D : CommAlgCat.{u} (baseRing C)) :
    (algSpec R).obj (op (restrictScalars C D)) ⟶ (algSpec R).obj (op C) :=
  (algSpec R).map (toRestrict D).op

theorem map_structurePoint {D D' : CommAlgCat.{u} (baseRing C)} (f : D ⟶ D') :
    (algSpec R).map (restrictScalarsMap f).op ≫ structurePoint D = structurePoint D' := by
  rw [structurePoint, ← Functor.map_comp, ← op_comp, toRestrict_comp]

end Coordinates

section TwistedPoint

variable (a : AutomorphicAction (Diagonalizable.groupScheme R M).toGrp G)
  {T : Over (Spec R)} (cx cy : a.Cocycle T)

/-- The twisted action `h · g = cy(h) a_h(g) cx(h)⁻¹` on points over a test `b : V ⟶ T`. -/
def twistedPoint {V : Over (Spec R)} (b : V ⟶ T)
    (h : V ⟶ (Diagonalizable.groupScheme R M).X) (g : V ⟶ G.X) : V ⟶ G.X :=
  AutomorphicAction.Cocycle.eval cy b h * a.act h g *
    (AutomorphicAction.Cocycle.eval cx b h)⁻¹

omit [IsAffine G.X.left] in
theorem twistedPoint_naturality {V V' : Over (Spec R)} (v : V' ⟶ V) (b : V ⟶ T)
    (h : V ⟶ (Diagonalizable.groupScheme R M).X) (g : V ⟶ G.X) :
    v ≫ twistedPoint a cx cy b h g = twistedPoint a cx cy (v ≫ b) (v ≫ h) (v ≫ g) := by
  simp only [twistedPoint, MonObj.comp_mul, GrpObj.comp_inv,
    AutomorphicAction.Cocycle.eval_naturality, a.naturality]

private theorem mul_mul_inv_eq_iff {Γ : Type*} [Group Γ] (y z x g : Γ) :
    y * z * x⁻¹ = g ↔ g * x * z⁻¹ = y := by
  constructor
  · rintro rfl
    group
  · rintro rfl
    group

omit [IsAffine G.X.left] in
/-- The fixed equation of the twisted action is the evaluated conjugacy equation. -/
theorem twistedPoint_eq_iff {V : Over (Spec R)} (b : V ⟶ T)
    (h : V ⟶ (Diagonalizable.groupScheme R M).X) (g : T ⟶ G.X) :
    twistedPoint a cx cy b h (b ≫ g) = b ≫ g ↔
      (AutomorphicAction.Cocycle.conjugate g cx).eval b h = cy.eval b h := by
  rw [AutomorphicAction.Cocycle.eval_conjugate, a.act_inv, twistedPoint]
  exact mul_mul_inv_eq_iff _ _ _ _

omit [IsAffine G.X.left] in
theorem twistedPoint_restrict {T' V : Over (Spec R)} (b' : T' ⟶ T) (b : V ⟶ T')
    (h : V ⟶ (Diagonalizable.groupScheme R M).X) (g : V ⟶ G.X) :
    twistedPoint a (AutomorphicAction.Cocycle.restrict b' cx)
      (AutomorphicAction.Cocycle.restrict b' cy) b h g = twistedPoint a cx cy (b ≫ b') h g := by
  simp only [twistedPoint, AutomorphicAction.Cocycle.eval_restrict]

end TwistedPoint

section AffineExt

variable {a : AutomorphicAction (Diagonalizable.groupScheme R M).toGrp G}

omit [IsAffine G.X.left] in
/-- Cocycles over an affine test agree once they agree at every character over every
algebra refinement of the test. -/
theorem cocycle_ext_affine {c d : a.Cocycle ((algSpec R).obj (op C))}
    (h : ∀ (D : CommAlgCat.{u} R) (φ : C ⟶ D) (t : Multiplicative M →* Dˣ),
      c.eval ((algSpec R).map φ.op) (characterPoint t) =
        d.eval ((algSpec R).map φ.op) (characterPoint t)) :
    c = d := by
  let T := (algSpec R).obj (op C)
  let H := (Diagonalizable.groupScheme R M).toGrp.X
  have : IsAffine T.left := by
    change IsAffine (Spec (CommRingCat.of C))
    infer_instance
  have : IsAffine H.left := by
    change IsAffine (Spec (CommRingCat.of (AddMonoidAlgebra R M)))
    infer_instance
  have : IsAffine (T ⊗ H).left := by
    change IsAffine (CategoryTheory.Limits.pullback T.hom H.hom)
    infer_instance
  have hW : (algSpec R).essImage (T ⊗ H) := essImage_algSpec.mpr (by infer_instance)
  let D := hW.witness.unop
  let e : (algSpec R).obj (op D) ≅ T ⊗ H := hW.getIso
  let φ : C ⟶ D := (algSpec.fullyFaithful.preimage (e.hom ≫ fst T H)).unop
  have hφ : (algSpec R).map φ.op = e.hom ≫ fst T H := algSpec.fullyFaithful.map_preimage _
  let t := Corepresented.affinePointsEquiv (Diagonalizable.functor R M)
    (Diagonalizable.grpCorepresentation R M) D (e.hom ≫ snd T H)
  have ht : characterPoint t = e.hom ≫ snd T H := MulEquiv.symm_apply_apply _ _
  have key := h D φ t
  rw [AutomorphicAction.Cocycle.eval, AutomorphicAction.Cocycle.eval, hφ, ht, ← comp_lift,
    lift_fst_snd, Category.comp_id] at key
  apply AutomorphicAction.Cocycle.ext
  exact (cancel_epi e.hom).1 key

end AffineExt

section Action

variable (a : AutomorphicAction (Diagonalizable.groupScheme R M).toGrp G)
  (cx cy : a.Cocycle ((algSpec R).obj (op C)))

/-- The twisted character action `t · g = cy(t) a_t(g) cx(t)⁻¹` on the points of `G` over
`C`-algebras, written on the base change `C ⊗[R] A` of the coordinate algebra. -/
def cocycleAction :
    Action (R := baseRing C) (M := M) (baseChange C (AffineCoordinates.algebra G)) where
  act {D} t p := ofCoordinatePoint (twistedPoint a cx cy (structurePoint D)
    (characterPoint (restrictChar t)) (coordinatePoint p))
  one {D} p := by
    apply coordinatePoint_injective
    rw [coordinatePoint_ofCoordinatePoint, restrictChar_one, characterPoint_one, twistedPoint,
      AutomorphicAction.Cocycle.eval_one, AutomorphicAction.Cocycle.eval_one, a.act_one_left,
      one_mul, inv_one, mul_one]
  mul {D} t s p := by
    apply coordinatePoint_injective
    simp only [coordinatePoint_ofCoordinatePoint, restrictChar_mul, characterPoint_mul,
      twistedPoint, AutomorphicAction.Cocycle.eval_mul, a.act_mul_left, a.act_mul_right,
      a.act_inv]
    group
  naturality {D D'} f t p := by
    apply coordinatePoint_injective
    rw [coordinatePoint_ofCoordinatePoint, coordinatePoint_comp, coordinatePoint_comp,
      coordinatePoint_ofCoordinatePoint, twistedPoint_naturality, map_structurePoint,
      ← mapCharacter_restrictChar, characterPoint_mapCharacter]

theorem coordinatePoint_cocycleAction {D : CommAlgCat.{u} (baseRing C)}
    (t : Multiplicative M →* Dˣ) (p : baseChange C (AffineCoordinates.algebra G) ⟶ D) :
    coordinatePoint ((cocycleAction a cx cy).act t p) =
      twistedPoint a cx cy (structurePoint D) (characterPoint (restrictChar t))
        (coordinatePoint p) :=
  coordinatePoint_ofCoordinatePoint _

/-- **Lifting conjugacies through nilpotent thickenings.** Let the coordinate algebra of `G`
be formally smooth and `I` a nilpotent ideal of `C`. A point `g₀` over `C ⧸ I` conjugating the
restriction of `cx` to that of `cy` lifts to a point over `C` conjugating `cx` to `cy`. -/
theorem exists_conjugate_lift [Algebra.FormallySmooth R (AffineCoordinates.algebra G)]
    (I : Ideal C) (hI : IsNilpotent I)
    (g₀ : (algSpec R).obj (op (CommAlgCat.of R (C ⧸ I))) ⟶ G.X)
    (hg₀ : AutomorphicAction.Cocycle.conjugate g₀
        (AutomorphicAction.Cocycle.restrict
          ((algSpec R).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I)).op) cx) =
      AutomorphicAction.Cocycle.restrict
        ((algSpec R).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I)).op) cy) :
    ∃ g : (algSpec R).obj (op C) ⟶ G.X,
      (algSpec R).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I)).op ≫ g = g₀ ∧
        AutomorphicAction.Cocycle.conjugate g cx = cy := by
  let π := (algSpec R).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I)).op
  let A' : CommAlgCat.{u} (baseRing C) := CommAlgCat.of (baseRing C) (C ⧸ I)
  let C' : CommAlgCat.{u} (baseRing C) := CommAlgCat.of (baseRing C) C
  let isoA : restrictScalars C A' ≅ CommAlgCat.of R (C ⧸ I) :=
    restrictIso (C := C) (CommAlgCat.of R (C ⧸ I))
  let isoC : restrictScalars C C' ≅ C := restrictIso (C := C) C
  let act := cocycleAction a cx cy
  let x₀ : baseChange C (AffineCoordinates.algebra G) ⟶ A' :=
    ofCoordinatePoint ((algSpec R).map isoA.inv.op ≫ g₀)
  have hx₀ : IsFixed act x₀ := by
    intro D f t
    apply coordinatePoint_injective
    have hred : CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I) ≫ isoA.inv ≫ restrictScalarsMap f =
        toRestrict D := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro c
      exact f.hom.commutes c
    let β := (algSpec R).map (restrictScalarsMap f).op ≫ (algSpec R).map isoA.inv.op
    have hβ : β ≫ π = structurePoint D := by
      rw [structurePoint, ← hred]
      simp only [β, π, op_comp, Functor.map_comp, Category.assoc]
    have hfix := (twistedPoint_eq_iff a _ _ β (characterPoint (restrictChar t)) g₀).2
      (by rw [hg₀])
    rw [twistedPoint_restrict, hβ] at hfix
    rw [coordinatePoint_cocycleAction, coordinatePoint_comp, coordinatePoint_ofCoordinatePoint]
    simpa only [β, Category.assoc] using hfix
  obtain ⟨y, hyfix, hyred⟩ := exists_fixed_lift act (C := C') I hI x₀ hx₀
  refine ⟨(algSpec R).map isoC.hom.op ≫ coordinatePoint y, ?_, ?_⟩
  · have h₁ : isoC.hom ≫ CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I) =
        restrictScalarsMap (CommAlgCat.ofHom (Ideal.Quotient.mkₐ (baseRing C) I)) ≫
          isoA.hom := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro c
      rfl
    rw [← Category.assoc, ← Functor.map_comp, ← op_comp, h₁, op_comp, Functor.map_comp,
      Category.assoc, ← coordinatePoint_comp, hyred, coordinatePoint_ofCoordinatePoint,
      ← Category.assoc, ← Functor.map_comp, ← op_comp, Iso.inv_hom_id, op_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  · apply cocycle_ext_affine
    intro D φ t
    rw [← twistedPoint_eq_iff]
    let : Algebra C D := φ.hom.toRingHom.toAlgebra
    have : IsScalarTower R C D :=
      IsScalarTower.of_algebraMap_eq fun r => (φ.hom.commutes r).symm
    let E : CommAlgCat.{u} (baseRing C) := CommAlgCat.of (baseRing C) D
    let isoE : restrictScalars C E ≅ D := restrictIso (C := C) D
    let f' : C' ⟶ E := CommAlgCat.ofHom (Algebra.ofId C D)
    let t' : Multiplicative M →* Eˣ := t
    have h₂ := congrArg coordinatePoint (hyfix E f' t')
    rw [coordinatePoint_cocycleAction, coordinatePoint_comp] at h₂
    have h₃ := congrArg ((algSpec R).map isoE.hom.op ≫ ·) h₂
    rw [twistedPoint_naturality] at h₃
    have e₁ : toRestrict E ≫ isoE.hom = φ := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro c
      rfl
    have e₂ : mapCharacter isoE.hom (restrictChar (C := C) t') = t := by
      ext m
      rfl
    have e₃ : restrictScalarsMap f' ≫ isoE.hom = isoC.hom ≫ φ := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro c
      rfl
    have k₁ : (algSpec R).map isoE.hom.op ≫ structurePoint E = (algSpec R).map φ.op := by
      rw [structurePoint, ← Functor.map_comp, ← op_comp, e₁]
    have k₂ : (algSpec R).map isoE.hom.op ≫ characterPoint (restrictChar (C := C) t') =
        characterPoint t := by
      rw [← characterPoint_mapCharacter, e₂]
    have k₃ : (algSpec R).map isoE.hom.op ≫ (algSpec R).map (restrictScalarsMap f').op ≫
        coordinatePoint y =
          (algSpec R).map φ.op ≫ ((algSpec R).map isoC.hom.op ≫ coordinatePoint y) := by
      rw [← Category.assoc, ← Functor.map_comp, ← op_comp, e₃, op_comp, Functor.map_comp,
        Category.assoc]
    rw [k₁, k₂, k₃] at h₃
    exact h₃

end Action

end Langlands.GroupScheme.CharacterAction
