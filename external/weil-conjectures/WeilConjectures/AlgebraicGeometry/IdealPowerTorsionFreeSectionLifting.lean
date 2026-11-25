/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.Topology.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.IdealPowerQuotientAffineLiftingSection
import WeilConjectures.AlgebraicGeometry.IdealPowerTorsionFreeSectionRestriction
import WeilConjectures.Topology.GlueSheavesOfModules
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Lifting a section into an ideal-power-torsion-free module

Source: Stacks Project, Properties, Tags 01PM and 01PQ, torsion-free case.
(blueprint: lem-pc-ideal-power-torsion-free-section-lifting)
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

noncomputable local instance {X : Scheme.{u}} (F : X.Modules) {V W : X.Opens} (h : V ≤ W) :
    HSMul ((SheafOfModules.unit X.ringCatSheaf).val.obj (op V))
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map (homOfLE h).op).hom).obj
        (F.val.obj (op V))) (F.val.obj (op V)) where
  hSMul := @SMul.smul Γ(X, V) Γ(F, V) inferInstance

private theorem power_mono {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι] (n : ℕ) :
    Mono (idealSheafPower ι n).2 := by
  induction n using Nat.twoStepInduction with
  | zero => change Mono (𝟙 _); infer_instance
  | one => change Mono ι; infer_instance
  | more n _ ih =>
    change Mono (idealModuleProductι ι (idealSheafPower ι (n + 1)).1 ≫
      (idealSheafPower ι (n + 1)).2)
    have : Mono (idealModuleProductι ι (idealSheafPower ι (n + 1)).1) := by
      dsimp [idealModuleProductι]
      infer_instance
    infer_instance

private theorem power_injective {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι] (n : ℕ) (W : X.Opens) :
    Function.Injective ((idealSheafPower ι n).2.app W) := by
  have := power_mono ι n
  have : Mono (idealSheafPower ι n).2.val := (SheafOfModules.forget _).map_mono _
  exact PresheafOfModules.injective_of_mono _ _

set_option backward.isDefEq.respectTransparency false in
/-- A section of an ideal-power-torsion-free module is evaluated by an ideal-power map.

Source: Stacks Project, Properties, Tags 01PM and 01PQ.
(blueprint: lem-pc-ideal-power-torsion-free-section-lifting)

Proof: Construct the zero module as the free module on the empty type. Its zero
map into F is monic and quasi-coherent, and htf identifies its section image
with each ideal-power annihilator. Its cokernel projection is an isomorphism.
Apply the affine quotient-lifting theorem with this constant annihilator system,
and compose the local lifts with the inverse cokernel projection. Choose a finite
affine cover and increase the local degrees with r to their maximum. Monicity
of the recursive power inclusions, hr and hone ensure that this preserves
values at one. On an overlap W, restrict a power section to W intersect U.
Injectivity of the power inclusion identifies it with its scalar image times
one, so linearity and the common evaluation show equality of the two local
maps there. The torsion-free restriction theorem makes their values equal on W.
Sheaf morphism descent glues the maps, and sheaf separation on the finite cover
proves their global evaluation is s. Empty covers, empty opens and degree zero
are included. Quasi-separatedness is retained in the signature but is unused.
No object is constructed from an arbitrary unproved existence statement. -/
theorem ideal_power_torsionFree_section_lifting
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType] [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (one : ∀ n : ℕ, Γ((idealSheafPower ι n).1, U))
    (r : ∀ (n m : ℕ), n ≤ m →
      ((idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1))
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
    (hone : ∀ n : ℕ, (idealSheafPower ι n).2.app U (one n) = (1 : Γ(X, U)))
    (hr : ∀ (n m : ℕ) (h : n ≤ m),
      r n m h ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2)
    (htf : ∀ (n : ℕ) (W : X.Opens) (x : F.val.obj (op W)),
      (∀ (V : X.Opens) (h : V ≤ W)
        (b : (idealSheafPower ι n).1.val.obj (op V)),
        ((idealSheafPower ι n).2.val.app (op V) b : Γ(X, V)) •
          F.val.map (homOfLE h).op x = 0) → x = 0) :
    ∀ s : Γ(F, U), ∃ (n : ℕ) (ψ : (idealSheafPower ι n).1 ⟶ F),
      ψ.app U (one n) = s := by
  classical
  intro s
  let Z : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) PEmpty.{u + 1}
  have hz : Limits.IsZero Z := by
    apply (Limits.IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext i
    exact PEmpty.elim i
  let a : Z ⟶ F := 0
  have hmono : Mono a := ⟨fun _ _ _ ↦ hz.eq_of_tgt _ _⟩
  have hqc : Z.IsQuasicoherent := by
    dsimp [Z]
    infer_instance
  have hann (n : ℕ) (W : X.Opens) (x : Γ(F, W)) :
      x ∈ Set.range (a.app W) ↔
        ∀ (V : X.Opens) (h : V ≤ W) (b : Γ((idealSheafPower ι n).1, V)),
          (F.smul (U := V) ((idealSheafPower ι n).2.val.app (op V) b)).asHom.hom
            (F.presheaf.map (homOfLE h).op x) = 0 := by
    constructor
    · rintro ⟨z, rfl⟩
      intro V h b
      have ha : a.app W z = 0 := rfl
      rw [ha, map_zero, map_zero]
    · intro hx
      have he : x = 0 := htf n W x hx
      exact ⟨0, by simpa [a] using he.symm⟩
  have hquot (n : ℕ) (W : X.Opens) (_ : W ≤ U) :
      Function.Bijective ((Limits.cokernel.π a).app W) := by
    have : IsIso (Limits.cokernel.π a) := by dsimp [a]; infer_instance
    exact ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation X.ringCatSheaf (op W)).map (Limits.cokernel.π a))
  have rone (n m : ℕ) (h : n ≤ m) (W : X.Opens) (hWU : W ≤ U) :
      (r n m h).app W
          (((idealSheafPower ι m).1).presheaf.map (homOfLE hWU).op (one m)) =
        ((idealSheafPower ι n).1).presheaf.map (homOfLE hWU).op (one n) := by
    apply power_injective ι n W
    have hone' (k : ℕ) :
        (idealSheafPower ι k).2.app W
            (((idealSheafPower ι k).1).presheaf.map (homOfLE hWU).op (one k)) =
          X.presheaf.map (homOfLE hWU).op (1 : Γ(X, U)) := by
      exact (PresheafOfModules.naturality_apply
        (idealSheafPower ι k).2.val (homOfLE hWU).op (one k)).trans
          (congrArg (X.presheaf.map (homOfLE hWU).op) (hone k))
    change (r n m h ≫ (idealSheafPower ι n).2).app W _ = _
    rw [hr, hone', hone']
  obtain ⟨S, hfin, hcover⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
      ⟨isCompact_univ (X := X), isOpen_univ⟩
  have hcover' : (⨆ V : S, V.1.1) = ⊤ := by
    ext x
    simpa using (Set.ext_iff.mp hcover x).symm
  have := hfin.to_subtype
  let := Fintype.ofFinite S
  have hlift (V : S) := ideal_power_quotient_affine_lifting_section
    ι F U one hU hone (fun _ ↦ Z) (fun _ ↦ a) (fun _ ↦ hmono)
    (fun _ ↦ hqc) hann hquot V.1 s
  choose k φ hφ using hlift
  have : IsIso (Limits.cokernel.π a) := by dsimp [a]; infer_instance
  let p : Limits.cokernel a ⟶ F := inv (Limits.cokernel.π a)
  have hπp : Limits.cokernel.π a ≫ p = 𝟙 F := IsIso.hom_inv_id _
  let n := Finset.univ.sup k
  have hkn (V : S) : k V ≤ n := Finset.le_sup (Finset.mem_univ V)
  let α (V : S) : ((idealSheafPower ι n).1).over V.1.1 ⟶ F.over V.1.1 :=
    (r (k V) n (hkn V)).over V.1.1 ≫ φ V ≫ p.over V.1.1
  have hα (V : S) (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V.1.1) :
      (α V).val.app (op (Over.mk (homOfLE hWV)))
          (((idealSheafPower ι n).1).presheaf.map (homOfLE hWU).op (one n)) =
        F.presheaf.map (homOfLE hWU).op s := by
    change p.app W ((φ V).val.app (op (Over.mk (homOfLE hWV)))
      ((r (k V) n (hkn V)).app W _)) = _
    rw [rone, ← hφ V W hWU hWV]
    change (Limits.cokernel.π a ≫ p).app W _ = _
    rw [hπp]
    rfl
  have hagree (V V' : S) (W : X.Opens) (hWV : W ≤ V.1.1) (hWV' : W ≤ V'.1.1) :
      (α V).val.app (op (Over.mk (homOfLE hWV))) =
        (α V').val.app (op (Over.mk (homOfLE hWV'))) := by
    ext b
    apply ideal_power_torsionFree_section_restriction ι F U hU htf W
    let T := W ⊓ U
    let j : T ⟶ W := homOfLE inf_le_left
    let oneT := ((idealSheafPower ι n).1).presheaf.map
      (homOfLE (inf_le_right : T ≤ U)).op (one n)
    let bT := ((idealSheafPower ι n).1).presheaf.map j.op b
    let c : Γ(X, T) := (idealSheafPower ι n).2.app T bT
    have honeT : (idealSheafPower ι n).2.app T oneT = (1 : Γ(X, T)) := by
      dsimp [oneT]
      erw [PresheafOfModules.naturality_apply, hone]
      exact map_one (X.presheaf.map (homOfLE inf_le_right).op).hom
    have hbT : bT = c • oneT := by
      apply power_injective ι n T
      rw [Modules.Hom.app_smul, honeT]
      exact (mul_one c).symm
    have nat (V : S) (hWV : W ≤ V.1.1) :
        F.presheaf.map j.op ((α V).val.app (op (Over.mk (homOfLE hWV))) b) =
          (α V).val.app (op (Over.mk (homOfLE (inf_le_left.trans hWV)))) bT := by
      exact (PresheafOfModules.naturality_apply (α V).val
        (Over.homMk j : Over.mk (homOfLE (inf_le_left.trans hWV)) ⟶
          Over.mk (homOfLE hWV)).op b).symm
    change F.presheaf.map j.op
        ((α V).val.app (op (Over.mk (homOfLE hWV))) b) =
      F.presheaf.map j.op ((α V').val.app (op (Over.mk (homOfLE hWV'))) b)
    erw [nat V hWV, nat V' hWV', hbT, map_smul, map_smul,
      hα V T inf_le_right, hα V' T inf_le_right]
  obtain ⟨ψ, hψ, _⟩ := (glue_sheaves_of_modules X.toRingedSpace S
    (fun V ↦ V.1.1) hcover').1 _ _ α hagree
  refine ⟨n, ψ, ?_⟩
  let T : TopCat.Sheaf Ab X := ⟨F.presheaf, F.isSheaf⟩
  apply T.eq_of_locally_eq' (fun V : S ↦ U ⊓ V.1.1) U
    (fun V ↦ homOfLE inf_le_left)
    (by simp only [← inf_iSup_eq, hcover', inf_top_eq, le_refl])
  intro V
  change F.presheaf.map (homOfLE inf_le_left).op (ψ.val.app (op U) (one n)) =
    F.presheaf.map (homOfLE inf_le_left).op s
  erw [← PresheafOfModules.naturality_apply ψ.val]
  have he := congrArg (fun f ↦ f.val.app
    (op (Over.mk (homOfLE (inf_le_right : U ⊓ V.1.1 ≤ V.1.1))))) (hψ V)
  change (ψ.over V.1.1).val.app (op (Over.mk (homOfLE inf_le_right))) _ = _
  rw [he]
  exact hα V _ inf_le_left inf_le_right

end AlgebraicGeometry.Scheme
