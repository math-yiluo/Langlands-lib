/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import all WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPowerQuotient
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitKernel

/-! # Reflection of cokernel torsion on a closed thickening

Source: Stacks Project, Tags 088A and 0888.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem product_zero_of_epi {X : Scheme.{u}} {J F Q : X.Modules}
    (j : J ⟶ SheafOfModules.unit X.ringCatSheaf) (p : F ⟶ Q) [Epi p]
    (h : IsZero (Scheme.idealModuleProduct j F)) :
    IsZero (Scheme.idealModuleProduct j Q) := by
  have := idealModuleProduct_mono j Q
  apply IsZero.of_mono_eq_zero (Scheme.idealModuleProductι j Q)
  have hz := (idealModuleProduct_quotient_comp_zero_iff j p (𝟙 Q)).mpr
    (h.eq_zero_of_src _)
  simpa using hz

set_option backward.isDefEq.respectTransparency false in
private theorem supported_of_power_zero {X : Scheme.{u}}
    (K : X.IdealSheafData) (q : ℕ) (F : X.Modules)
    (h : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι q).2 F)) :
    IsZero (Scheme.idealModuleProduct (K ^ q).subschemeι.ker.toModulesι F) := by
  let i := (K ^ q).subschemeι
  let adj := Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction i)
  obtain ⟨e, he⟩ := closedImmersion_power_quotient K q i
    (Scheme.IdealSheafData.ker_subschemeι (K ^ q)) adj F
  have : IsIso (formalModuleQuotientπ K q F) := by
    exact CokernelCofork.IsColimit.isIso_π
      (CokernelCofork.ofπ (cokernel.π _) (cokernel.condition _))
      (cokernelIsCokernel _) (h.eq_zero_of_src _)
  have : IsIso (adj.unit.app F) := by
    rw [← he]
    infer_instance
  obtain ⟨_, w, _⟩ := Scheme.Modules.closedImmersion_unit_kernel i F
  have := idealModuleProduct_mono i.ker.toModulesι F
  apply IsZero.of_mono_eq_zero (Scheme.idealModuleProductι i.ker.toModulesι F)
  apply (cancel_mono (adj.unit.app F)).mp
  simpa only [Scheme.idealModuleProductι, Scheme.idealModuleProduct, adj, zero_comp] using w

private theorem supported_completion_faithful {X Z : Scheme.{u}}
    [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] (I : X.IdealSheafData)
    (hc : ∀ hZ : IsNoetherian Z,
      Functor.IsEquivalence (@completion Z hZ (I.comap i))) :
    let P : ObjectProperty (CoherentModules X) := fun F ↦ CoherentModuleSupportedOn F i
    (P.ι ⋙ ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace) ⋙
      formalCompletionFunctor I).Faithful := by
  classical
  let hZ : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType i
  have : (completion Z (I.comap i)).IsEquivalence := hc hZ
  let P : ObjectProperty (CoherentModules X) := fun F ↦ CoherentModuleSupportedOn F i
  let U := P.ι ⋙ ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace)
  let H := U ⋙ formalCompletionFunctor I
  obtain ⟨E, ⟨β⟩⟩ := closedImmersion_coherent_equivalence i
  have : (Scheme.Modules.pushforward i).Faithful :=
    ⟨fun {G G'} ↦ ((closedImmersion_pushforward_fullyFaithful i).2 G G').1⟩
  obtain ⟨θ, _⟩ := (closedImmersion_coherentFormal_equivalence i I).2
  have hr : (ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace) ⋙
      formalCompletionFunctor (I.comap i) ⋙
        (Functor.whiskeringRight ℕᵒᵖ Z.Modules X.Modules).obj
          (Scheme.Modules.pushforward i)).Faithful := by
    change (completion Z (I.comap i) ⋙ ObjectProperty.ι (IsCoherentFormalModule (I.comap i)) ⋙
      (Functor.whiskeringRight ℕᵒᵖ Z.Modules X.Modules).obj
        (Scheme.Modules.pushforward i)).Faithful
    infer_instance
  have hl : (ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace) ⋙
      Scheme.Modules.pushforward i ⋙ formalCompletionFunctor I).Faithful :=
    Functor.Faithful.of_iso θ.symm
  let δ : E.functor ⋙ H ≅ ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace) ⋙
      Scheme.Modules.pushforward i ⋙ formalCompletionFunctor I :=
    (Functor.associator E.functor U (formalCompletionFunctor I)).symm ≪≫
      Functor.isoWhiskerRight β (formalCompletionFunctor I)
  have : (E.functor ⋙ H).Faithful := Functor.Faithful.of_iso δ.symm
  apply H.faithful_of_comp_essSurj E.functor
  intro A B f g hfg
  rw [← E.functor.map_preimage f, ← E.functor.map_preimage g]
  congr 1
  apply (E.functor ⋙ H).map_injective
  simpa using hfg

set_option backward.isDefEq.respectTransparency false in
/-- Completion on a fixed closed thickening reflects a uniform cokernel torsion bound.
Source: Stacks Project, Tag 088A, the second use of Remark 0888 and the identification
of coherent modules killed by the thickening ideal (Tag 087T).
https://stacks.math.columbia.edu/tag/088A
https://stacks.math.columbia.edu/tag/0888
(blueprint: lem-weil-pbc-completion-thickening-cokernel-reflection).

Proof: let Q be the ordinary cokernel of a and B = K^s Q, with inclusion j : B → Q.
Coherent cokernel closure and quasi-coherent submodule closure give coherence of Q and B.
The quotient G → Q carries annihilation by K^q to Q; its submodule B inherits this bound.
The closed-immersion power-quotient and unit-kernel comparisons identify these bounds
with support on Z = V(K^q). The coherent closed-pushforward equivalence and its natural
completion comparison transport faithful completion on Z to faithful completion on the
supported coherent modules of X. For every n the reduced cokernel of a surjects onto
Q/I^(n+1)Q, so the latter is killed by K^s. Naturality of ideal products then gives
j followed by Q → Q/I^(n+1)Q equal to zero. The cokernel universal property shows that
every reduction of j is zero. Faithful completion therefore gives j = 0, hence B = 0.
Finally formalModuleQuotient_factor at the identity of Q factors the inclusion K^(2s)Q
through K^s Q and proves the requested vanishing. No affine completion exactness or
kernel torsion hypothesis is used. In fact the cokernel argument does not need hF.
-/
theorem completion_thickening_cokernel_reflection
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (q : ℕ) (hq : 1 ≤ q)
    (hcomplete : ∀ hZ : IsNoetherian (K ^ q).subscheme,
      Functor.IsEquivalence
        (@completion ((K ^ q).subscheme) hZ (I.comap (K ^ q).subschemeι)))
    (F G : CoherentModules X) (a : F ⟶ G)
    (hF : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι q).2
      F.obj))
    (hG : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι q).2
      G.obj))
    (s : ℕ) (hs : 1 ≤ s)
    (hred : ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2
        (cokernel (formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1)))))) :
    IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (2 * s)).2
      (cokernel a.hom)) := by
  have _ := hF
  have _ := hq
  have _ := hs
  let Q := cokernel a.hom
  let p : G.obj ⟶ Q := cokernel.π a.hom
  have hp : Epi p := inferInstanceAs (Epi (cokernel.π _))
  have hcoh := Scheme.Modules.isCoherent_kernel_cokernel_biprod_and_submodule X
  have hQ : RingedSpace.IsCoherent X.toRingedSpace Q :=
    ((hcoh.1 F.obj G.obj F.property G.property).1 a.hom).2
  have : Q.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X Q).mp hQ).1
  let j := Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι s).2 Q
  let B := Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2 Q
  have hj : Mono j := idealModuleProduct_mono _ Q
  have : (Scheme.idealSheafPower K.toModulesι s).1.IsQuasicoherent :=
    idealSheafPower_quasicoherent K s
  have : B.IsQuasicoherent := idealModuleProduct_quasicoherent _ Q
  have hB : RingedSpace.IsCoherent X.toRingedSpace B :=
    (hcoh.2 Q B j hQ hj inferInstance).1
  have hQs : IsZero (Scheme.idealModuleProduct
      (K ^ q).subschemeι.ker.toModulesι Q) :=
    product_zero_of_epi _ p (supported_of_power_zero K q G.obj hG)
  have hBs : IsZero (Scheme.idealModuleProduct
      (K ^ q).subschemeι.ker.toModulesι B) :=
    idealModuleProduct_zero_of_mono _ j hQs
  have hcompleted : formalCompletionMap I j = formalCompletionMap I (0 : B ⟶ Q) := by
    apply NatTrans.ext
    funext n
    let b := formalModuleQuotientMap I p (Nat.le_refl (n.unop + 1))
    have hb : formalModuleQuotientπ I (n.unop + 1) G.obj ≫ b =
        p ≫ formalModuleQuotientπ I (n.unop + 1) Q := by
      simp [b, formalModuleQuotientMap, formalModuleQuotientπ]
    have : Epi (formalModuleQuotientπ I (n.unop + 1) Q) :=
      inferInstanceAs (Epi (cokernel.π _))
    have : Epi b := epi_of_epi_fac hb
    have hz : formalModuleQuotientMap I a.hom (Nat.le_refl (n.unop + 1)) ≫ b = 0 := by
      dsimp only [b]
      rw [← formalModuleQuotientMap_comp]
      simp [p, formalModuleQuotientMap]
    let e := cokernel.desc
      (formalModuleQuotientMap I a.hom (Nat.le_refl (n.unop + 1))) b hz
    have : Epi e := epi_of_epi_fac (cokernel.π_desc _ b hz)
    have hlevel := product_zero_of_epi (Scheme.idealSheafPower K.toModulesι s).2
      e (hred n.unop)
    obtain ⟨k, hk⟩ := formalModuleQuotient_factor K
      (formalModuleQuotientπ I (n.unop + 1) Q) (Nat.le_refl s)
    have hjzero : j ≫ formalModuleQuotientπ I (n.unop + 1) Q = 0 := by
      rw [hk, hlevel.eq_zero_of_src (Scheme.idealModuleProductι
        (Scheme.idealSheafPower K.toModulesι s).2
        (formalModuleQuotient I (n.unop + 1) Q)), comp_zero]
    change formalModuleQuotientMap I j (Nat.le_refl (n.unop + 1)) =
      formalModuleQuotientMap I (0 : B ⟶ Q) (Nat.le_refl (n.unop + 1))
    apply (cancel_epi (cokernel.π (Scheme.idealModuleProductι
      (Scheme.idealSheafPower I.toModulesι (n.unop + 1)).2 B))).mp
    dsimp only [B]
    simpa only [formalModuleQuotientMap, cokernel.π_desc, zero_comp] using hjzero
  let P : ObjectProperty (CoherentModules X) :=
    fun H ↦ CoherentModuleSupportedOn H (K ^ q).subschemeι
  let B' : P.FullSubcategory := ⟨⟨B, hB⟩, hBs⟩
  let Q' : P.FullSubcategory := ⟨⟨Q, hQ⟩, hQs⟩
  let f : B' ⟶ Q' := ObjectProperty.homMk (ObjectProperty.homMk j)
  let z : B' ⟶ Q' := ObjectProperty.homMk (ObjectProperty.homMk (0 : B ⟶ Q))
  let H := P.ι ⋙ ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace) ⋙
    formalCompletionFunctor I
  have : H.Faithful := supported_completion_faithful (K ^ q).subschemeι I hcomplete
  have hf : f = z := H.map_injective hcompleted
  have hjzero : j = 0 := congrArg (fun t : B' ⟶ Q' ↦ t.hom.hom) hf
  have hzero : IsZero B := IsZero.of_mono_eq_zero j hjzero
  obtain ⟨k, hk⟩ := formalModuleQuotient_factor K (𝟙 Q)
    (show s ≤ 2 * s by omega)
  have := idealModuleProduct_mono (Scheme.idealSheafPower K.toModulesι (2 * s)).2 Q
  apply IsZero.of_mono_eq_zero
    (Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι (2 * s)).2 Q)
  simpa only [Category.comp_id, hzero.eq_zero_of_src
    (Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι s).2 Q), comp_zero]
    using hk

end AlgebraicGeometry
