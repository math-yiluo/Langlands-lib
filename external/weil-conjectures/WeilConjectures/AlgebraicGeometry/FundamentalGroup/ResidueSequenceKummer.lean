/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ResidueSequence

/-!
# Residues of Kummer torsors

Let `U` be a nonempty connected open of an integral scheme `C` over a field `k`, `N` invertible
in `k` and `ζ ∈ k` a primitive `N`-th root of unity. For a unit `g` on `U`, the Kummer torsor of
`N`-th roots of `g` (`AlgebraicGeometry.Scheme.EtaleTorsor.kummer`) has residue
`ord_z g mod N` against `ζ` at every point `z` of `C`
(`AlgebraicGeometry.Scheme.EtaleTorsor.exists_residue_eq_ord_of_isUnit`): an `N`-th root of `g`
in a separable closure of `k(C)` is a Kummer element of the torsor. This produces the torsors
with prescribed residues in the residue sequence of blueprint
`proposition-no-fixed-class-degree-one--1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry.Scheme.EtaleTorsor

open FiniteEtale

variable {C U : Scheme.{u}} [IsIntegral C] (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U]

local notation "Ω" => SeparableClosure (Scheme.functionField C)

/-- The restriction `Γ(U, 𝒪_U) → k(C)` of the functions on a nonempty open `U` of an integral
scheme `C` to its generic point. -/
noncomputable def toFunctionField : Γ(U, ⊤) →+* C.functionField :=
  (Spec.preimage (genericPointLift j ≫ U.toSpecΓ)).hom

lemma specMap_toFunctionField :
    Spec.map (CommRingCat.ofHom (toFunctionField j)) = genericPointLift j ≫ U.toSpecΓ :=
  Spec.map_preimage _

/-- The restriction to the generic point of a global function on `C`, restricted to `U`, is its
germ at the generic point. -/
lemma toFunctionField_appTop (r : Γ(C, ⊤)) :
    toFunctionField j (j.appTop r) = C.presheaf.germ ⊤ (genericPoint C) trivial r := by
  have h : j.appTop ≫ CommRingCat.ofHom (toFunctionField j) =
      C.presheaf.germ ⊤ (genericPoint C) trivial := by
    apply Spec.map_injective
    rw [Spec.map_comp, specMap_toFunctionField, Category.assoc, ← Scheme.toSpecΓ_naturality,
      genericPointLift_comp_assoc]
    exact fromSpecStalk_toSpecΓ C (genericPoint C)
  exact congrArg (fun φ : Γ(C, ⊤) ⟶ CommRingCat.of C.functionField ↦ φ r) h

/-- The restriction to the generic point of a section of `𝒪_C` over an open `W ⊇ U`, restricted
to `U`, is its germ at the generic point. -/
lemma toFunctionField_appTop_topIso_inv (W : C.Opens) (m : U ⟶ W.toScheme) (hm : m ≫ W.ι = j)
    (s : Γ(C, W)) (hW : genericPoint C ∈ W) :
    toFunctionField j (m.appTop (W.topIso.inv s)) = C.presheaf.germ W (genericPoint C) hW s := by
  have hgm : genericPointLift j ≫ m = W.fromSpecStalkOfMem (genericPoint C) hW := by
    rw [← cancel_mono W.ι, Category.assoc, hm, genericPointLift_comp,
      Scheme.Opens.fromSpecStalkOfMem_ι]
  have h : W.topIso.inv ≫ m.appTop ≫ CommRingCat.ofHom (toFunctionField j) =
      C.presheaf.germ W (genericPoint C) hW := by
    apply Spec.map_injective
    simp only [Spec.map_comp, specMap_toFunctionField, Category.assoc]
    rw [← Scheme.toSpecΓ_naturality_assoc, reassoc_of% hgm,
      ← Scheme.Opens.fromSpecStalkOfMem_toSpecΓ]
    rfl
  exact congrArg (fun φ : Γ(C, W) ⟶ CommRingCat.of C.functionField ↦ φ s) h

variable [IsLocallyNoetherian C] {k : Type u} [Field k] (p : C ⟶ Spec (.of k)) {N : ℕ}
  [NeZero N] [NeZero (N : k)] [HasEnoughRootsOfUnity k N] [ConnectedSpace U]

-- instance search through `SeparableClosure` is slow
/-- Blueprint `proposition-no-fixed-class-degree-one--1`: residues of Kummer torsors.

For a unit `g` on a nonempty connected open `U` of `C` and a primitive `N`-th root of unity `ζ`
of `k`, the Kummer torsor of `N`-th roots of `g` has residue `ord_z g mod N` against `ζ` at
every point `z` of `C`. -/
theorem exists_residue_eq_ord_of_isUnit {ζ : k} (hζ : IsPrimitiveRoot ζ N) {g : Γ(U, ⊤)}
    (hg : IsUnit g) :
    ∃ T : EtaleTorsor (ULift.{u + 1} (ZMod N)) U, ∀ z : C,
      T.residue j p z (Additive.ofMul hζ.toRootsOfUnity) =
        (C.ord (toFunctionField j g) z : ZMod N) := by
  classical
  have hN : (N : k) ≠ 0 := NeZero.ne _
  set c : k →+* Γ(U, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ (j ≫ p).appTop).hom with hcdef
  have hn : IsUnit (N : Γ(U, ⊤)) := by simpa using hN.isUnit.map c
  set ζU := c ζ
  have hζU : ζU ^ N = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  set s := (Etale.genericGeometricPoint (C := C) j : Spec (.of Ω) ⟶ _)
  have hs : pointRingHom s =
      CommRingCat.ofHom (toFunctionField j) ≫ CommRingCat.ofHom (algebraMap _ Ω) := by
    apply Spec.map_injective
    rw [Spec.map_preimage, Spec.map_comp, specMap_toFunctionField]
    simp only [s, Etale.genericGeometricPoint, pointOfAlgebra, Category.assoc]
  have hc (r : k) : (pointRingHom s).hom (c r) =
      algebraMap C.functionField Ω (p.functionFieldConstants r) := by
    rw [hs]
    change algebraMap C.functionField Ω (toFunctionField j (c r)) = _
    congr 1
    rw [hcdef, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.comp_appTop,
      CommRingCat.hom_comp, RingHom.comp_apply, toFunctionField_appTop]
    rfl
  have hζs : IsPrimitiveRoot ((pointRingHom s).hom ζU) N := by
    rw [hc]
    exact hζ.map_of_injective
      ((algebraMap C.functionField Ω).comp p.functionFieldConstants).injective
  let T := EtaleTorsor.kummer ζU hζU hn hg s hζs
  refine ⟨T, fun z ↦ ?_⟩
  -- a point of `T` over the generic geometric point and the corresponding ring map
  set t := T.genericFiberPoint j
  have ht : t ≫ T.π = s := T.genericFiberPoint_comp j
  set α : CommRingCat.of (KummerAlgebra U N g) ⟶ CommRingCat.of Ω :=
    Spec.preimage (t ≫ pullback.snd _ _)
  have hα : kummerStructureMap N g ≫ α = pointRingHom s := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Category.assoc, ← pullback.condition,
      ← Category.assoc]
    exact congrArg (· ≫ U.toSpecΓ) ht
  have hαr (r : Γ(U, ⊤)) : α (algebraMap _ _ r) = (pointRingHom s).hom r :=
    congrArg (fun φ : Γ(U, ⊤) ⟶ CommRingCat.of Ω ↦ φ r) hα
  -- the Kummer element `x = α(T)`
  set x := α (AdjoinRoot.root _)
  have hx : x ^ N = algebraMap C.functionField Ω (toFunctionField j g) := by
    have hr := AdjoinRoot.eval₂_root (X ^ N - Polynomial.C g : Γ(U, ⊤)[X])
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at hr
    rw [← map_pow, hr]
    refine (hαr g).trans ?_
    rw [hs]
    rfl
  have hx0 : x ≠ 0 := by
    intro h0
    have hu := (hg.map (toFunctionField j)).map (algebraMap C.functionField Ω)
    rw [← hx, h0, zero_pow (NeZero.ne N)] at hu
    exact not_isUnit_zero hu
  refine T.residue_eq_ord j p z _ hx0 hx.symm fun σ ↦ ?_
  have hσ := T.specMap_comp_eq_comp_vadd_galoisCharacter j σ t ht
  set m := (T.galoisCharacter j σ).val
  have hσα : α ≫ CommRingCat.ofHom (σ : Ω →+* Ω) =
      CommRingCat.ofHom (kummerAlgHom ζU hζU (f := g) m).toRingHom ≫ α := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, ← Category.assoc, hσ, Category.assoc]
    change t ≫ kummerVadd ζU hζU m ≫ pullback.snd _ _ = _
    rw [kummerVadd, pullback.lift_snd, Category.assoc]
  have h := congrArg (fun φ : CommRingCat.of (KummerAlgebra U N g) ⟶ CommRingCat.of Ω ↦
    φ (AdjoinRoot.root _)) hσα
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, kummerAlgHom_root, map_mul, map_pow] at h
  change σ x = _
  rw [h, hαr, hc]
  simp [x, m]

end AlgebraicGeometry.Scheme.EtaleTorsor
