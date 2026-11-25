/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndSurjective
public import WeilConjectures.CategoryTheory.Preadditive.FinitePowerCokernel
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections

/-!
# The global sections of the condensed ring `ℚ̲̄_ℓ`

The global sections `Γ ℚ̲̄_ℓ = (𝟙 ⟶ ℚ̲̄_ℓ)` of the condensed ring `ℚ̲̄_ℓ` are the constant ones: the
ring homomorphism `ℚ̄_ℓ →+* Γ ℚ̲̄_ℓ` (`Profinite.PadicAlgCl.constRingHom`) is surjective
(`Profinite.PadicAlgCl.constRingHom_surjective`). Indeed the monoidal unit of condensed abelian
groups is the sheafification of the constant presheaf `ℤ`, and a morphism of presheaves out of
`ℤ` is determined by the image of `1` at the point `*` (`Profinite.natTrans_ext_of_app_one`), `*`
being terminal among profinite sets. The value at `*` of a global section of `ℚ̲̄_ℓ` is an element
of `ℚ̲̄_ℓ(*) = ℚ̄_ℓ`.

Consequently the endomorphisms of the regular module `ℚ̲̄_ℓ` form a quotient of the field `ℚ̄_ℓ`,
and it is nonzero: every nonzero endomorphism of the regular module is invertible
(`Profinite.PadicAlgCl.isIso_of_ne_zero_end_regular`), and `𝟙 ≠ 0`
(`Profinite.PadicAlgCl.one_ne_zero_end_regular`).
-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory MonObj Opposite

namespace CategoryTheory.Sheaf

attribute [local instance] Sheaf.monoidalCategory

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [HasSheafify J Ab.{w}]
  [(J.W (A := Ab.{w})).IsMonoidal] [J.HasSheafCompose (forget₂ RingCat.{w} Ab.{w})]
  (S : Sheaf J RingCat.{w}) {R : Type*} [Ring R]

/-- On underlying presheaves, after the unit `ε : 𝟙 ⟶ (𝟙 : Sheaf J Ab).val`, the global section
`ringHomΓSheafCompose J S φ hφ r` of the sheaf of rings `S` is the global section
`n ↦ n • φ X r` of the underlying presheaf of rings. -/
lemma ε_comp_ringHomΓSheafCompose_hom (φ : ∀ X, R →+* S.obj.obj X)
    (hφ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R), S.obj.map f (φ X r) = φ Y r) (r : R) :
    ε (sheafToPresheaf J Ab.{w}) ≫
        (sheafToPresheaf J Ab.{w}).map (ringHomΓSheafCompose J S φ hφ r).hom =
      (S.obj.ringHomΓCompForget₂ φ hφ r).hom := by
  have e (G : Sheaf J Ab.{w}) (c : 𝟙_ (Sheaf J Ab.{w}) ⟶ G) :
      ((sheafificationAdjunction J Ab.{w}).homEquiv _ _).symm
        (ε (sheafToPresheaf J Ab.{w}) ≫ (sheafToPresheaf J Ab.{w}).map c) =
        Functor.OplaxMonoidal.η (presheafToSheaf J Ab.{w}) ≫ c := by
    rw [Adjunction.homEquiv_naturality_right_symm]
    congr 1
    exact Equiv.symm_apply_apply _ _
  apply ((sheafificationAdjunction J Ab.{w}).homEquiv _ _).symm.injective
  rw [e, Adjunction.homEquiv_counit]
  simp [ringHomΓSheafCompose, sheafifyRingPresheafIso, Functor.Monoidal.η_ε_assoc]

end CategoryTheory.Sheaf

namespace Profinite

open Functor.LaxMonoidal

/-- A morphism of abelian presheaves on profinite sets out of the monoidal unit (the constant
presheaf `ℤ`) is determined by the image of `1` at the point. -/
lemma natTrans_ext_of_app_one {P : Profinite.{u}ᵒᵖ ⥤ Ab.{w}}
    {t s : 𝟙_ (Profinite.{u}ᵒᵖ ⥤ Ab.{w}) ⟶ P}
    (h : t.app (op (Profinite.of PUnit.{u + 1})) (ULift.up 1) =
      s.app (op (Profinite.of PUnit.{u + 1})) (ULift.up 1)) : t = s := by
  have key (t : 𝟙_ (Profinite.{u}ᵒᵖ ⥤ Ab.{w}) ⟶ P) (X : Profinite.{u}ᵒᵖ) (n : ULift.{w} ℤ) :
      t.app X n = n.down • P.map (isTerminalPUnit.from X.unop).op
        (t.app (op (Profinite.of PUnit.{u + 1})) (ULift.up 1)) := by
    have hn : n = n.down • (ULift.up 1 : ULift.{w} ℤ) := by
      ext
      simp
    conv_lhs => rw [hn, map_zsmul]
    rw [← NatTrans.naturality_apply]
    rfl
  ext X n
  rw [key t, key s, h]

end Profinite

open Limits

namespace Profinite.PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Every global section of the condensed ring `ℚ̲̄_ℓ` is constant. -/
theorem constRingHom_surjective : Function.Surjective (constRingHom.{u} ℓ) := by
  intro x
  let adj := sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}
  let x' := adj.homEquiv _ _
    (inv (Functor.LaxMonoidal.ε (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
      ≫ x.hom)
  let b := x'.app (op (Profinite.of PUnit.{u + 1})) (ULift.up 1)
  refine ⟨b.down.1 PUnit.unit, ?_⟩
  have hx : x' = (Functor.ringHomΓCompForget₂ (padicAlgClCondensedRing ℓ).obj
      (constSectionRingHom ℓ) (fun _ _ ↦ rfl) (b.down.1 PUnit.unit)).hom := by
    ext S n
    obtain ⟨m⟩ := n
    have key : x'.app S (ULift.up 1) = (padicAlgClRingObj ℓ).obj.map
        (isTerminalPUnit.from S.unop).op b :=
      NatTrans.naturality_apply x' (isTerminalPUnit.from S.unop).op (ULift.up 1)
    have hm : (ULift.up m : ULift.{u + 1} ℤ) = m • ULift.up 1 := by
      ext
      simp
    refine (congrArg (x'.app S) hm).trans ?_
    rw [map_zsmul, key]
    exact (zsmul_eq_mul (α := (padicAlgClRingPresheaf ℓ).obj S) _ m).trans rfl
  ext1
  rw [constRingHom, Sheaf.ringHomΓSheafCompose, RingHom.comp_apply, RingHom.comp_apply,
    Γ.map_hom, Γ.mapFunctor_hom, ← hx, Category.assoc, Sheaf.sheafifyRingPresheafIso, asIso_hom,
    ← Adjunction.homEquiv_counit, Equiv.symm_apply_apply, IsIso.hom_inv_id_assoc]

/-- The identity of the regular module `ℚ̲̄_ℓ` is not zero: the sections of `ℚ̲̄_ℓ` over the point
form the nonzero ring `ℚ̄_ℓ`. -/
theorem one_ne_zero_end_regular :
    (1 : End (Mod.regular (padicAlgClRingObj.{u} ℓ))) ≠ 0 := by
  intro h
  have h1 : 𝟙 (padicAlgClRingObj.{u} ℓ) = 0 := congrArg Mod.Hom.hom congr($(h).asHom)
  exact one_ne_zero (α := ULift.{u + 1}
    (_root_.PadicAlgCl.finiteIntermediateFieldValued ℓ (Profinite.of PUnit.{u + 1})))
    (congrArg (fun φ ↦ φ.hom.app (op (Profinite.of PUnit.{u + 1}))
      (1 : (padicAlgClRingPresheaf.{u} ℓ).obj (op (Profinite.of PUnit.{u + 1})))) h1)

/-- Every nonzero endomorphism of the regular module `ℚ̲̄_ℓ` is invertible: the endomorphisms are
the multiplications by the constants `ℚ̄_ℓ`, a field. -/
theorem isIso_of_ne_zero_end_regular (t : End (Mod.regular (padicAlgClRingObj.{u} ℓ)))
    (ht : t ≠ 0) : IsIso t.asHom :=
  isIso_of_ne_zero_of_surjective (Mod.regularEndRingHom.comp (constRingHom.{u} ℓ))
    (Mod.regularEndRingHom_surjective.comp (constRingHom_surjective ℓ)) t ht

end Profinite.PadicAlgCl
