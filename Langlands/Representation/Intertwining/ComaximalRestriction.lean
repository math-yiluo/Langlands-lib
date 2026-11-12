import Langlands.Representation.Intertwining.PQRegularity
import Langlands.Representation.Smooth.Schur.Proof

/-! # Restriction of intertwiners under comaximal central kernels -/

noncomputable section

universe uH uB uV uW

namespace Langlands.Intertwining

variable {H : Type uH} [Group H] {B : Type uB} [Monoid B]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ H V} {τ : Representation ℂ H W}

/-- The inclusion of a subrepresentation. -/
def subtypeIntertwiner (S : Subrepresentation ρ) :
    S.toRepresentation.IntertwiningMap ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

/-- The projection onto the quotient by a subrepresentation. -/
def quotientIntertwiner (S : Subrepresentation ρ) :
    ρ.IntertwiningMap (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) where
  toLinearMap := S.toSubmodule.mkQ
  isIntertwining' _ := by ext; rfl

/-- Restrict an intertwining map to a subrepresentation of its source. -/
def restriction (S : Subrepresentation ρ) :
    (ρ.IntertwiningMap τ) →ₗ[ℂ] (S.toRepresentation.IntertwiningMap τ) where
  toFun f := f.comp (subtypeIntertwiner S)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Intertwiners commute with the action of the group algebra of any mapped monoid. -/
theorem algebraAction_natural (f : ρ.IntertwiningMap τ) (a : B →* H)
    (t : MonoidAlgebra ℂ B) (v : V) :
    f (Representation.asAlgebraHom (ρ.comp a) t v) =
      Representation.asAlgebraHom (τ.comp a) t (f v) := by
  induction t using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b c =>
    simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply,
      MonoidHom.comp_apply, map_smul, f.isIntertwining]

/-- An element of a central monoid algebra acts by an intertwining endomorphism. -/
def centralAction (a : B →* H) (ha : ∀ b g, a b * g = g * a b)
    (t : MonoidAlgebra ℂ B) : ρ.IntertwiningMap ρ where
  toLinearMap := Representation.asAlgebraHom (ρ.comp a) t
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change Representation.asAlgebraHom (ρ.comp a) t (ρ g v) =
      ρ g (Representation.asAlgebraHom (ρ.comp a) t v)
    induction t using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | single b c =>
      simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply,
        MonoidHom.comp_apply, map_smul]
      rw [← Module.End.mul_apply, ← map_mul, ha, map_mul, Module.End.mul_apply]

/-- An element killing the quotient sends every vector into the subrepresentation. -/
theorem algebraAction_mem_of_quotientKernel (S : Subrepresentation ρ) (a : B →* H)
    (t : MonoidAlgebra ℂ B)
    (ht : t ∈ groupAlgebraKernel (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) a)
    (v : V) : Representation.asAlgebraHom (ρ.comp a) t v ∈ S := by
  apply (Submodule.Quotient.mk_eq_zero S.toSubmodule).mp
  have ht0 := (mem_groupAlgebraKernel_iff _ _ _).mp ht
  have h := algebraAction_natural (quotientIntertwiner S) a t v
  rw [ht0, LinearMap.zero_apply] at h
  exact h

/-- Restriction is bijective if the target kernel and the source-quotient kernel are
comaximal in a central monoid algebra. -/
theorem restriction_bijective_of_comaximal (S : Subrepresentation ρ) (a : B →* H)
    (ha : ∀ b g, a b * g = g * a b)
    (h : groupAlgebraKernel τ a ⊔
      groupAlgebraKernel (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) a = ⊤) :
    Function.Bijective (restriction (τ := τ) S) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp
    ((Ideal.eq_top_iff_one _).mp h)
  have hx0 := (mem_groupAlgebraKernel_iff _ _ _).mp hx
  have hy1 : Representation.asAlgebraHom (τ.comp a) y = 1 := by
    have hsum := congrArg (Representation.asAlgebraHom (τ.comp a)) hxy
    simpa [hx0] using hsum
  let E : ρ.IntertwiningMap S.toRepresentation :=
    { toLinearMap := (centralAction (ρ := ρ) a ha y).toLinearMap.codRestrict S.toSubmodule
        (algebraAction_mem_of_quotientKernel S a y hy)
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact congrArg (fun t : V →ₗ[ℂ] V => t v)
          ((centralAction (ρ := ρ) a ha y).isIntertwining' g) }
  have hfy (f : ρ.IntertwiningMap τ) (v : V) :
      f (E v) = f v := by
    change f (Representation.asAlgebraHom (ρ.comp a) y v) = f v
    rw [algebraAction_natural, hy1]
    rfl
  constructor
  · intro f g hfg
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change f v = g v
    rw [← hfy f v, ← hfy g v]
    exact congrArg (fun F : S.toRepresentation.IntertwiningMap τ => F (E v)) hfg
  · intro f
    refine ⟨f.comp E, ?_⟩
    ext s
    change f (E (s : V)) = f s
    have hs := algebraAction_natural (subtypeIntertwiner S) a y s
    have heq : E (s : V) = Representation.asAlgebraHom (S.toRepresentation.comp a) y s := by
      apply Subtype.ext
      exact hs.symm
    rw [heq, algebraAction_natural, hy1]
    rfl

/-- The canonical linear equivalence given by restriction under comaximal central kernels. -/
def restrictionEquivOfComaximal (S : Subrepresentation ρ) (a : B →* H)
    (ha : ∀ b g, a b * g = g * a b)
    (h : groupAlgebraKernel τ a ⊔
      groupAlgebraKernel (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) a = ⊤) :
    (ρ.IntertwiningMap τ) ≃ₗ[ℂ] (S.toRepresentation.IntertwiningMap τ) :=
  LinearEquiv.ofBijective (restriction S) (restriction_bijective_of_comaximal S a ha h)

/-- Precomposition by an equivalence identifies a Hom space with an endomorphism space. -/
def endomorphismEquiv (e : ρ.Equiv τ) :
    (ρ.IntertwiningMap τ) ≃ₗ[ℂ] (τ.IntertwiningMap τ) where
  toFun f := f.comp e.symm.toIntertwiningMap
  invFun f := f.comp e.toIntertwiningMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by ext v; exact congrArg f (e.symm_apply_apply v)
  right_inv f := by ext v; exact congrArg f (e.apply_symm_apply v)

/-- If the retained subrepresentation is an admissible irreducible target, the Hom space
has complex dimension one. -/
theorem finrank_intertwining_eq_one_of_comaximal [TopologicalSpace H]
    (S : Subrepresentation ρ) (a : B →* H)
    (ha : ∀ b g, a b * g = g * a b)
    (h : groupAlgebraKernel τ a ⊔
      groupAlgebraKernel (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) a = ⊤)
    (e : S.toRepresentation.Equiv τ) (hadm : IsAdmissible τ) (hirr : τ.IsIrreducible) :
    Module.finrank ℂ (ρ.IntertwiningMap τ) = 1 := by
  obtain ⟨E⟩ := admissibleSchur_homEquiv τ hadm hirr τ (Representation.Equiv.refl τ)
  let F := (restrictionEquivOfComaximal S a ha h).trans ((endomorphismEquiv e).trans E)
  exact F.finrank_eq.trans (Module.finrank_self ℂ)

end Langlands.Intertwining
