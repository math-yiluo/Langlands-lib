/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import all WeilConjectures.AlgebraicGeometry.FormalSystemsPullback
import all WeilConjectures.AlgebraicGeometry.TorsionControlledFormalRestriction
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Restricting one torsion-controlled local model

Source: Stacks Project, Tag 0889(1), Zariski locality by uniqueness; equation 0880.
(blueprint: lem-weil-pbc-torsion-local-model-restriction).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem coherent_of_iso {X : Scheme.{u}} [IsNoetherian X]
    {F G : X.Modules} (e : F ≅ G)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) :
    RingedSpace.IsCoherent X.toRingedSpace F := by
  have hh := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X G).mp hG
  apply (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mpr
  have ht : SheafOfModules.IsFiniteType.{u} F := by
    obtain ⟨p, hp⟩ := hh.2.exists_localGeneratorsData
    have : p.IsFiniteType := hp
    let p' : F.LocalGeneratorsData :=
      { I := p.I
        X := p.X
        coversTop := p.coversTop
        generators i := (p.generators i).ofEpi (e.inv.over (p.X i)) }
    have hp' : p'.IsFiniteType := by
      constructor
      intro i
      have := hp.isFiniteType i
      dsimp [p']
      infer_instance
    constructor
    exact ⟨p', hp'⟩
  exact ⟨(SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm hh.1, ht⟩

set_option backward.isDefEq.respectTransparency false in
/-- A single local coherent model restricts, with its actual torsion bounds and
normalized quotient maps, to every smaller open. This asserts no comparison map
between different local models.

Source: Stacks Project, Tag 0889(1), first sentence of proof; equation 0880.
(blueprint: lem-weil-pbc-torsion-local-model-restriction).

Proof: Let f : W → U be the open immersion, R its restriction functor, and T
its tensor pullback. Their adjunctions to the same pushforward give t : T ≅ R.
Construct Fw = R(F). The proved coherent_pullback helper of FormalSystemsPullback
and invariance under isomorphism prove coherence. Set lw = overMapCompOverEquiv(L)
followed by R(l). The over-site comparisons and hHlocal identify R(Hlocal) with Hw;
call that isomorphism eH, and define aw = R(a) followed by eH. Naturality of
overMapCompOverEquiv and R(hb), followed by cancellation of the comparison
isomorphisms, prove the required b equation.

The proved powerQuotientIso helpers of FormalSystemsPullback construct a normalized
completion comparison for T(F). Conjugate by t to obtain gamma for R(F). Naturality
of t, powerQuotientIso_π, and the cokernel descent equation show that R(π) followed
by gamma is π for R(F). Assemble beta_w using overFunctorMap inverse,
overMapCompOverEquiv, overFunctorEquiv U, R(beta), and gamma. To check q, postcompose
with beta_w, cancel overFunctorMap, use naturality of overMapCompOverEquiv and R(hq),
cancel R(beta inverse) against R(beta), and apply the normalized gamma equation.

The actual kernel and cokernel of a are quasi-coherent. The proved
powerProduct_pullback_zero helper transfers their zero ideal-power products to T;
the powerProduct_zero_of_iso helper of TorsionControlledFormalRestriction transfers
them through t. Restriction preserves kernels and cokernels, and postcomposition
with eH preserves their isomorphism classes. Transfer the zero products through
these comparisons to get the same positive exponent for aw. The ideal on W is
identified using comap_comp and homOfLE_ι. Nothing assumes a cover or affineness;
empty opens, zero modules, and zero or unit ideals use these same constructions.
-/
theorem torsionLocalModel_restriction
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (U W : X.Opens) (h : W ≤ U)
    (Hlocal F : CoherentModules U.toScheme)
    (hHlocal : Hlocal.obj = (Scheme.Modules.restrictFunctor U.ι).obj H.obj)
    (a : F ⟶ Hlocal)
    (β : N.obj ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      formalCompletionSystem (J.comap U.ι) F.obj)
    (ha : ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower (J.comap U.ι).toModulesι s).2 (kernel a.hom)) ∧
      IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower (J.comap U.ι).toModulesι s).2 (cokernel a.hom)))
    (L : SheafOfModules ((moduleRings X.toRingedSpace).over U))
    (l : (Scheme.Modules.overEquiv U).functor.obj L ≅ F.obj)
    (b : L ⟶ H.obj.over U) (q : ∀ n : ℕᵒᵖ, L ⟶ (N.obj.obj n).over U)
    (hb : (Scheme.Modules.overEquiv U).functor.map b ≫
      (Scheme.Modules.overFunctorEquiv U).hom.app H.obj ≫ eqToHom hHlocal.symm =
        l.hom ≫ a.hom)
    (hq : ∀ n : ℕᵒᵖ, (Scheme.Modules.overEquiv U).functor.map (q n) ≫
      (Scheme.Modules.overFunctorEquiv U).hom.app (N.obj.obj n) =
        l.hom ≫ formalModuleQuotientπ (J.comap U.ι) (n.unop + 1) F.obj ≫ β.inv.app n)
    (Hw : CoherentModules W.toScheme)
    (hHw : Hw.obj = (Scheme.Modules.overEquiv W).functor.obj (H.obj.over W)) :
    ∃ (Fw : CoherentModules W.toScheme)
      (lw : (Scheme.Modules.overEquiv W).functor.obj
        ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE h : W ⟶ U)).obj L) ≅ Fw.obj)
      (aw : Fw ⟶ Hw)
      (βw : (N.obj ⋙ SheafOfModules.overFunctor (moduleRings X.toRingedSpace) W ⋙
          (Scheme.Modules.overEquiv W).functor) ≅
        formalCompletionSystem (J.comap W.ι) Fw.obj),
      (∃ s : ℕ, 1 ≤ s ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap W.ι).toModulesι s).2 (kernel aw.hom)) ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap W.ι).toModulesι s).2 (cokernel aw.hom))) ∧
      (Scheme.Modules.overEquiv W).functor.map
          ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
              (homOfLE h : W ⟶ U)).map b ≫
            (SheafOfModules.overFunctorMap (moduleRings X.toRingedSpace)
              (homOfLE h : W ⟶ U)).hom.app H.obj) ≫ eqToHom hHw.symm =
        lw.hom ≫ aw.hom ∧
      (∀ n : ℕᵒᵖ, (Scheme.Modules.overEquiv W).functor.map
          ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
              (homOfLE h : W ⟶ U)).map (q n) ≫
            (SheafOfModules.overFunctorMap (moduleRings X.toRingedSpace)
              (homOfLE h : W ⟶ U)).hom.app (N.obj.obj n)) =
        lw.hom ≫ formalModuleQuotientπ (J.comap W.ι) (n.unop + 1) Fw.obj ≫ βw.inv.app n) := by
  classical
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    (Scheme.Hom.isOpenEmbedding U.ι).isInducing.noetherianSpace
  let : IsNoetherian U.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  have : TopologicalSpace.NoetherianSpace W.toScheme :=
    (Scheme.Hom.isOpenEmbedding W.ι).isInducing.noetherianSpace
  let : IsNoetherian W.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  let f := X.homOfLE h
  let R := Scheme.Modules.restrictFunctor f
  let T := Scheme.Modules.tensorPullback f
  obtain ⟨t⟩ : Nonempty (T ≅ R) :=
    ⟨(Scheme.Modules.nonempty_tensorPullbackAdjunction f).some.leftAdjointUniq
      (Scheme.Modules.restrictAdjunction f)⟩
  let E := (Scheme.Modules.overEquiv W).functor
  let O := SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE h : W ⟶ U)
  obtain ⟨e⟩ : Nonempty (O ⋙ E ≅ (Scheme.Modules.overEquiv U).functor ⋙ R) :=
    ⟨Scheme.Modules.overMapCompOverEquiv (homOfLE h : W ⟶ U)⟩
  generalize hη : SheafOfModules.overFunctorMap (moduleRings X.toRingedSpace)
    (homOfLE h : W ⟶ U) = η
  generalize hηU : Scheme.Modules.overFunctorEquiv U = ηU at hb hq
  let Fw : CoherentModules W.toScheme :=
    ⟨R.obj F.obj, coherent_of_iso (t.app F.obj).symm (coherent_pullback f _ F.property)⟩
  let lw := e.app L ≪≫ R.mapIso l
  let eH : R.obj Hlocal.obj ≅ Hw.obj :=
    R.mapIso (eqToIso hHlocal) ≪≫ R.mapIso (ηU.app H.obj).symm ≪≫
      (e.app (H.obj.over U)).symm ≪≫ E.mapIso (η.app H.obj) ≪≫ eqToIso hHw.symm
  let aw : Fw ⟶ Hw := ObjectProperty.homMk (R.map a.hom ≫ eH.hom)
  have hJ : (J.comap U.ι).comap f = J.comap W.ι := by
    rw [← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]
  have hFq : F.obj.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType U.toScheme _).mp
      F.property).1
  obtain ⟨γ, hγ⟩ : ∃ γ : formalCompletionSystem (J.comap U.ι) F.obj ⋙ R ≅
      formalCompletionSystem (J.comap W.ι) Fw.obj,
      ∀ n : ℕᵒᵖ,
        R.map (formalModuleQuotientπ (J.comap U.ι) (n.unop + 1) F.obj) ≫ γ.hom.app n =
          formalModuleQuotientπ (J.comap W.ι) (n.unop + 1) Fw.obj := by
    rw [← hJ]
    let γ0 := Functor.isoWhiskerLeft (formalCompletionSystem (J.comap U.ι) F.obj) t.symm ≪≫
      (completionPullbackIso f (J.comap U.ι)).symm.app F ≪≫
      (formalCompletionFunctor ((J.comap U.ι).comap f)).mapIso (t.app F.obj)
    refine ⟨γ0, ?_⟩
    intro n
    change R.map (formalModuleQuotientπ (J.comap U.ι) (n.unop + 1) F.obj) ≫
      (t.app (formalModuleQuotient (J.comap U.ι) (n.unop + 1) F.obj)).inv ≫
        (powerQuotientIso f (J.comap U.ι) F.obj hFq (n.unop + 1)).inv ≫
          formalModuleQuotientMap ((J.comap U.ι).comap f) (t.app F.obj).hom
            (Nat.le_refl (n.unop + 1)) = _
    have ht := t.inv.naturality (formalModuleQuotientπ (J.comap U.ι)
      (n.unop + 1) F.obj)
    change R.map (formalModuleQuotientπ (J.comap U.ι) (n.unop + 1) F.obj) ≫
        (t.app (formalModuleQuotient (J.comap U.ι) (n.unop + 1) F.obj)).inv =
      (t.app F.obj).inv ≫ T.map (formalModuleQuotientπ (J.comap U.ι)
        (n.unop + 1) F.obj) at ht
    rw [reassoc_of% ht]
    rw [← powerQuotientIso_π f (J.comap U.ι) F.obj hFq (n.unop + 1)]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [show formalModuleQuotientπ ((J.comap U.ι).comap f) (n.unop + 1) (T.obj F.obj) ≫
        formalModuleQuotientMap ((J.comap U.ι).comap f) (t.app F.obj).hom
          (Nat.le_refl (n.unop + 1)) =
        (t.app F.obj).hom ≫ formalModuleQuotientπ ((J.comap U.ι).comap f)
          (n.unop + 1) (R.obj F.obj) from cokernel.π_desc _ _ _]
    simp [Fw]
  let α : SheafOfModules.overFunctor (moduleRings X.toRingedSpace) W ⋙ E ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ R :=
    Functor.isoWhiskerRight η.symm E ≪≫
      Functor.isoWhiskerLeft (SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U)
        e ≪≫ Functor.isoWhiskerRight ηU R
  let βw := Functor.isoWhiskerLeft N.obj α ≪≫ Functor.isoWhiskerRight β R ≪≫ γ
  refine ⟨Fw, lw, aw, βw, ?_, ?_, ?_⟩
  · obtain ⟨s, hs, hk, hc⟩ := ha
    have : F.obj.IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType U.toScheme _).mp
        F.property).1
    have : Hlocal.obj.IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType U.toScheme _).mp
        Hlocal.property).1
    have := Scheme.Modules.isQuasicoherent_kernel a.hom
    have := Scheme.Modules.isQuasicoherent_cokernel a.hom
    have hkT := powerProduct_pullback_zero f (J.comap U.ι) (kernel a.hom)
      (inferInstance) s hk
    have hcT := powerProduct_pullback_zero f (J.comap U.ι) (cokernel a.hom)
      (inferInstance) s hc
    rw [hJ] at hkT hcT
    have hkR := powerProduct_zero_of_iso (J.comap W.ι) (t.app (kernel a.hom)).symm s hkT
    have hcR := powerProduct_zero_of_iso (J.comap W.ι) (t.app (cokernel a.hom)).symm s hcT
    refine ⟨s, hs, ?_, ?_⟩
    · exact powerProduct_zero_of_iso (J.comap W.ι)
        (kernelCompMono (R.map a.hom) eH.hom ≪≫ (PreservesKernel.iso R a.hom).symm) s hkR
    · exact powerProduct_zero_of_iso (J.comap W.ι)
        (cokernelCompIsIso (R.map a.hom) eH.hom ≪≫
          (PreservesCokernel.iso R a.hom).symm) s hcR
  · have hbR := congrArg (fun z ↦ R.map z) hb
    simp only [Functor.map_comp] at hbR
    change R.map ((Scheme.Modules.overEquiv U).functor.map b) ≫
        R.map (ηU.app H.obj).hom ≫ R.map (eqToHom hHlocal.symm) =
      R.map l.hom ≫ R.map a.hom at hbR
    have hne := e.hom.naturality b
    change E.map (O.map b) ≫ (e.app (H.obj.over U)).hom =
      (e.app L).hom ≫ R.map ((Scheme.Modules.overEquiv U).functor.map b) at hne
    simp only [Functor.map_comp]
    dsimp only [lw, aw, eH, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      ObjectProperty.homMk, eqToIso.hom]
    simp only [Category.assoc]
    rw [← reassoc_of% hbR]
    rw [← R.map_comp_assoc (eqToHom hHlocal.symm) (eqToHom hHlocal)]
    simp only [eqToHom_trans, eqToHom_refl, R.map_id, Category.id_comp]
    rw [← R.map_comp_assoc (ηU.app H.obj).hom (ηU.app H.obj).inv]
    simp only [Iso.hom_inv_id, R.map_id, Category.id_comp]
    rw [← reassoc_of% hne]
    simp only [Iso.hom_inv_id_assoc]
    rfl
  · intro n
    apply (cancel_mono (βw.hom.app n)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    have hqR := congrArg (fun z ↦ R.map z) (hq n)
    simp only [Functor.map_comp] at hqR
    change R.map ((Scheme.Modules.overEquiv U).functor.map (q n)) ≫
        R.map (ηU.app (N.obj.obj n)).hom =
      R.map l.hom ≫ R.map (formalModuleQuotientπ (J.comap U.ι) (n.unop + 1) F.obj) ≫
        R.map (β.inv.app n) at hqR
    have hne := e.hom.naturality (q n)
    change E.map (O.map (q n)) ≫ (e.app ((N.obj.obj n).over U)).hom =
      (e.app L).hom ≫ R.map ((Scheme.Modules.overEquiv U).functor.map (q n)) at hne
    change E.map (O.map (q n) ≫ (η.app (N.obj.obj n)).hom) ≫
      E.map (η.app (N.obj.obj n)).inv ≫
        (e.app ((N.obj.obj n).over U)).hom ≫
          R.map (ηU.app (N.obj.obj n)).hom ≫ R.map (β.hom.app n) ≫ γ.hom.app n =
      lw.hom ≫ formalModuleQuotientπ (J.comap W.ι) (n.unop + 1) Fw.obj
    rw [E.map_comp]
    simp only [Category.assoc]
    rw [← E.map_comp_assoc (η.app (N.obj.obj n)).hom (η.app (N.obj.obj n)).inv,
      Iso.hom_inv_id, E.map_id, Category.id_comp]
    rw [reassoc_of% hne, reassoc_of% hqR]
    have hβ := (R.mapIso (β.app n)).inv_hom_id
    change R.map (β.inv.app n) ≫ R.map (β.hom.app n) = 𝟙 _ at hβ
    rw [reassoc_of% hβ, hγ n]
    exact (Category.assoc _ _ _).symm

end AlgebraicGeometry
