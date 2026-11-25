/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.ArtinSchreier
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.ArtinSchreierDataConstruction

/-!
# The Artin–Schreier sequence

Source: `literature/blueprint/master/blueprint/sec-curve-estimates/lem-sc-second-kummer-divisors/
lem-sc-as-sequence.md`, node `lemma-p-torsion-affine-curve-characteristic--3` (blueprint:
lemma-p-torsion-affine-curve-characteristic--3).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

set_option autoImplicit false

/-- Two étale sheaves of abelian groups whose sections are identified with the global functions,
compatibly with restriction, are isomorphic. -/
private noncomputable def sheafIsoOfSectionsEquiv {C : Scheme.{u}}
    (G H : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (b : ∀ U : C.Etaleᵒᵖ, H.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (ha : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (hb : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : H.obj.obj U),
      b V (H.obj.map g x) = g.unop.left.appTop (b U x)) :
    G ≅ H :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun U ↦ ((a U).trans (b U).symm).toAddCommGrpIso) fun {U V} g ↦ by
      ext x
      apply (b V).injective
      change b V ((b V).symm (a V (G.obj.map g x))) = b V (H.obj.map g ((b U).symm (a U x)))
      rw [AddEquiv.apply_symm_apply, ha, hb, AddEquiv.apply_symm_apply])

/-- The Artin–Schreier sequence `0 → ℤ/p → 𝔾ₐ → 𝔾ₐ → 0` on a curve over an algebraically closed
field of characteristic `p`, with its sectionwise maps specified. It is the sequence
`Scheme.artinSchreierSequence` of `AlgebraicGeometry.Sites.ArtinSchreier`, with `G = 𝔾ₐ`
(`Scheme.gaSheaf`), `wp = ℘` (`Scheme.gaArtinSchreier`) and `iota = Scheme.constantZModToGaSheaf`.
Source: Stacks Project, Étale Cohomology, Section 0A3J, and blueprint
`lemma-p-torsion-affine-curve-characteristic--3` (blueprint:
lemma-p-torsion-affine-curve-characteristic--3).

The isomorphism identifies `G` with the universe lift of the recorded étale
structure-module sheaf. The natural additive equivalences `a` identify its
sections with global functions, including their restriction maps. The equation
on the sheafification unit specifies the unique extension of `c ↦ c • 1`.

Proof: `p` is prime and vanishes in `Γ(C, 𝒪_C)`. The sequence `ker ℘ → 𝔾ₐ → 𝔾ₐ` is short exact
(`Scheme.artinSchreierSequence_shortExact`), and `ℤ/p → ker ℘` is an isomorphism
(`Scheme.isIso_constantZModToKernelGaArtinSchreier`). The sections of `𝔾ₐ` and of the lifted
structure-module sheaf are both the global functions, compatibly with restriction. -/
theorem artinSchreier_shortExact
    {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (p : ℕ) [CharP k p] (hp : 0 < p) :
    ∃ (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
      (_ : G ≅ (sheafCompose C.smallEtaleTopology
        AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (Scheme.Modules.etaleTensorSectionsSheaf (Scheme.Modules.unitObj C)))
      (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
      (wp : G ⟶ G) (iota : C.constantZMod p ⟶ G) (hzero : iota ≫ wp = 0),
      (∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
        a V (G.obj.map g x) = g.unop.left.appTop (a U x)) ∧
      (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
        a U (wp.hom.app U x) = (a U x) ^ p - a U x) ∧
      (∀ (U : C.Etaleᵒᵖ) (c : ZMod p),
        a U (iota.hom.app U
          ((toSheafify C.smallEtaleTopology
            ((Functor.const C.Etaleᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c))) =
          (c.val : Γ(U.unop.left, ⊤))) ∧
      ShortComplex.ShortExact (ShortComplex.mk iota wp hzero) := by
  have : NeZero p := ⟨hp.ne'⟩
  have : Fact p.Prime := CharP.char_is_prime_of_pos k p
  have hk : ((p : ℕ) : Γ(Spec (.of k), ⊤)) = 0 := by
    rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom, CharP.cast_eq_zero k p,
      map_zero]
  have hp0 : ((p : ℕ) : Γ(C, ⊤)) = 0 := by
    rw [← map_natCast f.appTop.hom, hk, map_zero]
  obtain ⟨G', hG', a', ha'⟩ := artinSchreier_construction C
  let a : ∀ U : C.Etaleᵒᵖ, C.gaSheaf.obj.obj U ≃+ Γ(U.unop.left, ⊤) := fun _ ↦ AddEquiv.ulift
  have ha : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : C.gaSheaf.obj.obj U),
      a V (C.gaSheaf.obj.map g x) = g.unop.left.appTop (a U x) := fun _ _ _ _ ↦ rfl
  let θ := C.constantZModToKernelGaArtinSchreier p hp0
  have : IsIso θ := C.isIso_constantZModToKernelGaArtinSchreier p hp0
  refine ⟨C.gaSheaf, sheafIsoOfSectionsEquiv _ _ a a' ha ha' ≪≫ hG', a,
    C.gaArtinSchreier p hp0, C.constantZModToGaSheaf p hp0,
    C.constantZModToGaSheaf_comp_gaArtinSchreier p hp0, ha, fun _ _ ↦ rfl, fun U c ↦ ?_, ?_⟩
  · change ULift.down (α := Γ(U.unop.left, ⊤)) (((toSheafify _ _ ≫
      (C.constantZModToGaSheaf p hp0).hom).app U) (ULift.up c)) = _
    rw [C.toSheafify_constantZModToGaSheaf p hp0]
    refine (C.zmodToGaPresheaf_app_apply p hp0 U c).trans ?_
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    rw [map_natCast, map_natCast]
  · refine ShortComplex.shortExact_of_iso ?_ (C.artinSchreierSequence_shortExact p hp0)
    refine ShortComplex.isoMk (asIso θ).symm (Iso.refl _) (Iso.refl _) ?_ ?_
    · dsimp [Scheme.artinSchreierSequence]
      rw [Category.comp_id, IsIso.inv_comp_eq]
      exact (kernel.lift_ι _ _ _).symm
    · dsimp [Scheme.artinSchreierSequence]
      rw [Category.comp_id, Category.id_comp]

end AlgebraicGeometry
