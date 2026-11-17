import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.HomDescent

/-! # Anti-affine groups and supplied affinization quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- An anti-affine field group has no global functions beyond those of its base. -/
def IsAntiAffine (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  IsIso G.X.hom.appTop

namespace IsAntiAffine

variable {G H : GroupScheme (Spec (CommRingCat.of k))} (hG : IsAntiAffine G)

include hG

/-- Every homomorphism from an anti-affine group to an affine group is trivial. -/
theorem hom_eq_zero [IsAffine H.X.left] (f : G ⟶ H) : f = 0 := by
  have : IsIso G.X.hom.appTop := hG
  have hu : G.X.hom.appTop ≫ η[G.X].left.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, η[G.X].w]
    rfl
  have : IsIso η[G.X].left.appTop := isIso_of_hom_comp_eq_id _ hu
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply ext_of_isAffine
  apply (cancel_mono η[G.X].left.appTop).mp
  simp only [← Scheme.Hom.comp_appTop]
  exact congrArg (fun x => x.left.appTop)
    ((IsMonHom.one_hom f.hom.hom).trans (IsMonHom.one_hom (0 : G ⟶ H).hom.hom).symm)

/-- Anti-affine groups satisfy the Library's all-test fixed-vector unipotence. -/
theorem isUnipotent : IsUnipotent G := by
  intro n _ _ _ ρ
  have : IsAffine (GeneralLinear.groupScheme n (CommRingCat.of k)).X.left :=
    GeneralLinear.isAffine_groupScheme n (CommRingCat.of k)
  have hρ : ρ = MatrixRepresentation.trivial G n := hom_eq_zero hG ρ
  subst ρ
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro he
    have := congrFun he (Classical.choice (inferInstance : Nonempty n))
    exact one_ne_zero this
  · intro T g
    rw [MatrixRepresentation.trivial_pointMatrix]
    exact Matrix.one_mulVec _

end IsAntiAffine

/-- A homomorphism is an affinization when its target is affine and it induces
an isomorphism on global sections. -/
structure IsAffinization {G Q : GroupScheme (Spec (CommRingCat.of k))} (q : G ⟶ Q) : Prop where
  isAffine : IsAffine Q.X.left
  isIso_appTop : IsIso q.hom.hom.left.appTop

namespace IsAffinization

variable {G Q : GroupScheme (Spec (CommRingCat.of k))} {q : G ⟶ Q}

/-- The affine target is canonically the spectrum of the source's global functions. -/
def targetIso (hq : IsAffinization q) :
    Q.X.left ≅ Spec Γ(G.X.left, ⊤) := by
  have := hq.isAffine
  have := hq.isIso_appTop
  exact Q.X.left.isoSpec ≪≫
    (Scheme.Spec.mapIso (asIso q.hom.hom.left.appTop).op).symm

/-- The specified homomorphism is the actual canonical affinization map under
`targetIso`. -/
theorem comp_targetIso (hq : IsAffinization q) :
    q.hom.hom.left ≫ (targetIso hq).hom = G.X.left.toSpecΓ := by
  have := hq.isAffine
  have := hq.isIso_appTop
  change q.hom.hom.left ≫ Q.X.left.toSpecΓ ≫
    (Scheme.Spec.mapIso (asIso q.hom.hom.left.appTop).op).inv = _
  rw [← Category.assoc, Scheme.toSpecΓ_naturality]
  simp

end IsAffinization

/-- Supplied geometry of the anti-affine affinization quotient of a smooth
connected field group. The existence assertion is separate. -/
structure AntiAffineQuotient (G : GroupScheme (Spec (CommRingCat.of k))) where
  group : GroupScheme (Spec (CommRingCat.of k))
  projection : G ⟶ group
  isAffinization : IsAffinization projection
  smooth : Smooth group.X.hom
  connectedSpace : ConnectedSpace group.X.left
  smooth_projection : Smooth projection.hom.hom.left
  surjective_projection : Surjective projection.hom.hom.left
  quasiCompact_projection : QuasiCompact projection.hom.hom.left
  smooth_kernel : Smooth (kernel projection).X.hom
  connectedSpace_kernel : ConnectedSpace (kernel projection).X.left
  antiAffine_kernel : IsAntiAffine (kernel projection)

end Langlands.GroupScheme
