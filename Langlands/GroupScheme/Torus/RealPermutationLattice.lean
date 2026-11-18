import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RepresentationTheory.Basic

/-! # Permutation lattice containing the lattice and a fixed evaluation coordinate -/

noncomputable section

namespace Langlands.GroupScheme.RealTorus

universe u

/-- A finite free lattice with a finite group action embeds as an abelian-group summand
of a permutation lattice. A chosen linear form fixed by a chosen group element can be
realized by evaluation at a coordinate fixed by that element. -/
def PermutationLatticeWithFixedCoordinateStatement : Prop :=
  ∀ (Γ M : Type u) [Group Γ] [Finite Γ] [AddCommGroup M]
    [Module.Free ℤ M] [Module.Finite ℤ M] (ρ : Representation ℤ Γ M)
    (σ : Γ) (d : M →+ ℤ), (∀ m, d (ρ σ m) = d m) →
    ∃ (I : Type u) (_ : Finite I) (_ : MulAction Γ I)
      (f : M →+ (I → ℤ)) (r : (I → ℤ) →+ M) (i : I),
      (∀ g m j, f (ρ g m) j = f m (g⁻¹ • j)) ∧
      (∀ m, r (f m) = m) ∧ σ • i = i ∧ (∀ m, f m i = d m)

section

variable {Γ M : Type u} [Group Γ] [AddCommGroup M] (ρ : Representation ℤ Γ M)

private def translate (g : Γ) (d : M →+ ℤ) : M →+ ℤ :=
  d.comp (ρ g⁻¹).toAddMonoidHom

private theorem translate_one (d : M →+ ℤ) : translate ρ 1 d = d := by
  ext m
  simp [translate]

private theorem translate_mul (g h : Γ) (d : M →+ ℤ) :
    translate ρ (g * h) d = translate ρ g (translate ρ h d) := by
  ext m
  simp [translate, mul_inv_rev, Module.End.mul_apply]

end

theorem permutationLatticeWithFixedCoordinate : PermutationLatticeWithFixedCoordinateStatement.{u} := by
  classical
  intro Γ M _ _ _ _ _ ρ σ d hd
  let b := Module.Free.chooseBasis ℤ M
  let := Module.Finite.finite_basis b
  let J := Module.Free.ChooseBasisIndex ℤ M
  let : Fintype J := Fintype.ofFinite J
  let seed : Option J → M →+ ℤ
    | none => d
    | some j => ((LinearMap.proj j).comp b.equivFun.toLinearMap).toAddMonoidHom
  let orbit := Set.range (fun p : Γ × Option J => translate ρ p.1 (seed p.2))
  let I := ↥orbit
  let index : Γ × Option J → I := fun p => ⟨_, ⟨p, rfl⟩⟩
  let : Finite I := Finite.of_surjective index (by
    rintro ⟨x, p, hp⟩
    exact ⟨p, Subtype.ext hp⟩)
  let action : MulAction Γ I :=
    { smul := fun g x => ⟨translate ρ g x.val, by
        obtain ⟨p, hp⟩ := x.property
        exact ⟨(g * p.1, p.2), (translate_mul ρ g p.1 (seed p.2)).trans
          (congrArg (translate ρ g) hp)⟩⟩
      one_smul := fun x => Subtype.ext (translate_one ρ x.val)
      mul_smul := fun g h x => Subtype.ext (translate_mul ρ g h x.val) }
  let := action
  let atSeed : Option J → I := fun j => ⟨seed j, ⟨(1, j), translate_one ρ _⟩⟩
  let f : M →+ (I → ℤ) :=
    { toFun := fun m i => i.val m
      map_zero' := funext fun i => i.val.map_zero
      map_add' := fun m n => funext fun i => i.val.map_add m n }
  let r : (I → ℤ) →+ M := b.equivFun.symm.toAddEquiv.toAddMonoidHom.comp
    { toFun := fun a j => a (atSeed (some j))
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  refine ⟨I, inferInstance, action, f, r, atSeed none, ?_, ?_, ?_, fun _ => rfl⟩
  · intro g m i
    change i.val (ρ g m) = i.val (ρ (g⁻¹)⁻¹ m)
    rw [inv_inv]
  · intro m
    change b.equivFun.symm (b.equivFun m) = m
    exact b.equivFun.symm_apply_apply m
  · apply Subtype.ext
    change translate ρ σ d = d
    ext m
    change d (ρ σ⁻¹ m) = d m
    rw [← hd (ρ σ⁻¹ m), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

end Langlands.GroupScheme.RealTorus
