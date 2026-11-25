/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.AffineAcyclic
public import WeilConjectures.AlgebraicGeometry.Sites.ArtinSchreier
public import WeilConjectures.AlgebraicGeometry.Sites.GaGmLowerStar

/-!
# Cohomology of `𝔾ₐ` and `ℤ/p` on a curve in degrees `≥ 2`

Let `C` be a curve over an algebraically closed field. An abelian étale sheaf `F` on `C` which
is acyclic on affine étale `C`-schemes has no cohomology in degrees `≥ 2`: the vanishing of `H²`
is `AlgebraicGeometry.IsCurve.subsingleton_sheafH_two_of_forall_isAffine`, and the higher degrees
follow by dimension shifting, since the cokernel of a monomorphism from `F` into an injective
sheaf is again acyclic on affine étale `C`-schemes. This applies to `𝔾ₐ`.

In characteristic `p`, the Artin–Schreier sequence `0 → ℤ/p → 𝔾ₐ → 𝔾ₐ → 0` then shows that
`Hᵠ(C, ℤ/p) = 0` for `q ≥ 3`, and that `H²(C, ℤ/p)` is the cokernel of `℘ = F - 1` on
`H¹(C, 𝔾ₐ)`.

## Main statements

- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_add_two_of_forall_isAffine`: sheaves acyclic on
  affine étale schemes have no cohomology in degrees `≥ 2`.
- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_gaSheaf`: `Hᵠ(C, 𝔾ₐ) = 0` for `q ≥ 2`.
- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_constantZMod`: `Hᵠ(C, ℤ/p) = 0` for `q ≥ 2`,
  provided `℘` is surjective on `H¹(C, 𝔾ₐ)`; for `q ≥ 3` this is unconditional.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsCurve

open Etale

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **Sheaves acyclic on affine étale schemes have no cohomology in degrees `≥ 2` on a curve.**
Let `C` be a curve over an algebraically closed field `k` and `F` an abelian étale sheaf on `C`
such that `Hᵠ(W, w^* F) = 0` for every étale `w : W ⟶ C` with `W` affine and every `q ≥ 1`. Then
`Hⁿ(C, F) = 0` for `n ≥ 2`. -/
theorem subsingleton_sheafH_add_two_of_forall_isAffine (f : C ⟶ Spec (.of k)) [IsCurve f]
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : ∀ (W : Scheme.{u}) (w : W ⟶ C), AlgebraicGeometry.Etale w → IsAffine W → ∀ q : ℕ,
      Subsingleton (Sheaf.H ((w)^*[AddCommGrpCat.{u + 1}].obj F) (q + 1))) (n : ℕ) :
    Subsingleton (Sheaf.H F (n + 2)) := by
  induction n generalizing F with
  | zero => exact subsingleton_sheafH_two_of_forall_isAffine f F hF
  | succ n ih =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : S.ShortExact :=
      .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    -- the cokernel `Q` is again acyclic on affine étale schemes
    have hQ : ∀ (W : Scheme.{u}) (w : W ⟶ C), AlgebraicGeometry.Etale w → IsAffine W →
        ∀ q : ℕ, Subsingleton (Sheaf.H ((w)^*[AddCommGrpCat.{u + 1}].obj S.X₃) (q + 1)) := by
      intro W w hw hW q
      let P := (w)^*[AddCommGrpCat.{u + 1}]
      have hS' := hS.map_of_exact P
      have : Injective (S.map P).X₂ := injective_upperStar_obj_of_etale_addCommGrp w S.X₂
      refine subsingleton_of_forall_eq 0 fun y ↦ ?_
      obtain ⟨x, rfl⟩ := (Sheaf.H.exact_map_δSucc hS' (q + 1) y).1
        (@Subsingleton.elim _ (hF W w hw hW (q + 1)) _ _)
      rw [Abelian.Ext.eq_zero_of_injective x, map_zero]
    have := ih S.X₃ hQ
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, rfl⟩ := (Sheaf.H.exact_δSucc_map hS (n + 2) x).1
      (Abelian.Ext.eq_zero_of_injective _)
    rw [Subsingleton.elim y 0, map_zero]

/-- **`𝔾ₐ` has no cohomology in degrees `≥ 2` on a curve.** For a curve `C` over an algebraically
closed field, `Hᵠ(C_ét, 𝔾ₐ) = 0` for `q ≥ 2`, since `𝔾ₐ` is acyclic on affine schemes
(`AlgebraicGeometry.Scheme.subsingleton_sheafH_gaSheaf_of_isAffine`). Neither smoothness nor
connectedness is needed. The identification `Hᵠ(C_ét, 𝔾ₐ) ≅ Hᵠ(C, 𝒪_C)` with Zariski cohomology
in the blueprint statement is not formalised here.
(blueprint: `proposition-p-torsion-smooth-proper-curve--3`, vanishing in degrees `≥ 2`) -/
theorem subsingleton_sheafH_gaSheaf (f : C ⟶ Spec (.of k)) [IsCurve f] (n : ℕ) :
    Subsingleton (Sheaf.H C.gaSheaf (n + 2)) :=
  subsingleton_sheafH_add_two_of_forall_isAffine f _ (fun W w _ _ q ↦
    have : Subsingleton ((Sheaf.functorH _ (q + 1)).obj W.gaSheaf) :=
      W.subsingleton_sheafH_gaSheaf_of_isAffine q
    ((Sheaf.functorH _ (q + 1)).mapIso
      (Scheme.upperStarGaSheafIso w)).addCommGroupIsoToAddEquiv.toEquiv.subsingleton) n

/-- **Artin–Schreier vanishing on a curve.** Let `C` be a curve over an algebraically closed
field of characteristic `p`. Then `Hᵠ(C, ℤ/p) = 0` for `q ≥ 3`, and `H²(C, ℤ/p) = 0` as soon as
the Artin–Schreier map `℘ = F - 1` is surjective on `H¹(C, 𝔾ₐ)`: in the long exact sequence of
`0 → ℤ/p → 𝔾ₐ → 𝔾ₐ → 0` the groups `Hᵠ(C, 𝔾ₐ)` vanish for `q ≥ 2`
(`AlgebraicGeometry.IsCurve.subsingleton_sheafH_gaSheaf`). For a proper smooth curve the
surjectivity of `℘` on the finite-dimensional `H¹(C, 𝒪_C)` is Lang–Steinberg; this part of the
blueprint statement, which needs the comparison with Zariski cohomology, is not formalised here.
(blueprint: `proposition-p-torsion-smooth-proper-curve--3`, reduction to `℘` on `H¹(C, 𝔾ₐ)`) -/
theorem subsingleton_sheafH_constantZMod (f : C ⟶ Spec (.of k)) [IsCurve f] (p : ℕ)
    [Fact p.Prime] (hp : (p : Γ(C, ⊤)) = 0) (q : ℕ) (hq : 2 ≤ q)
    (h℘ : q = 2 → Function.Surjective (Sheaf.H.map (C.gaArtinSchreier p hp) 1)) :
    Subsingleton (Sheaf.H (C.constantZMod p) q) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 + 1 := ⟨q - 2, by omega⟩
  have hS := C.artinSchreierSequence_shortExact p hp
  have h₂ : Subsingleton (Sheaf.H (C.artinSchreierSequence p hp).X₂ (n + 1 + 1)) :=
    subsingleton_sheafH_gaSheaf f n
  have hker : Subsingleton (Sheaf.H (kernel (C.gaArtinSchreier p hp)) (n + 1 + 1)) := by
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, rfl⟩ := (Sheaf.H.exact_δSucc_map hS (n + 1) x).1 (Subsingleton.elim _ _)
    rcases n with _ | n
    · obtain ⟨z, rfl⟩ := h℘ rfl y
      exact (Sheaf.H.exact_map_δSucc hS 1).apply_apply_eq_zero z
    · have : Subsingleton (Sheaf.H (C.artinSchreierSequence p hp).X₃ (n + 1 + 1)) :=
        subsingleton_sheafH_gaSheaf f n
      rw [Subsingleton.elim y 0, map_zero]
  let e := C.constantZModIsoKernelGaArtinSchreier p hp
  exact (Function.LeftInverse.injective (f := Sheaf.H.map e.hom (n + 1 + 1))
    (g := Sheaf.H.map e.inv (n + 1 + 1))
    fun x ↦ by rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]).subsingleton

end AlgebraicGeometry.IsCurve
