/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ThickeningSystemPushforward
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import all WeilConjectures.AlgebraicGeometry.AffinePushforwardIdealProduct
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardIdealPowers
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-! # Adic conditions for the explicit pushforward system

Source: Stacks Project, Cohomology of Schemes, Remark 088F, Lemma 087T, equation 0880.
(blueprint: lem-weil-pbc-thickening-system-pushforward-adic).
-/

@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry
noncomputable section
set_option autoImplicit false

open CategoryTheory.Limits MonoidalCategory Opposite Scheme.Modules in
set_option backward.isDefEq.respectTransparency false in
/-- The recursively constructed power is a submodule: each product inclusion is monic,
and composition preserves monomorphisms. -/
private theorem power_inclusion_mono {X : Scheme.{v}} (J : X.IdealSheafData) (n : ℕ) :
    Mono (Scheme.idealSheafPower J.toModulesι n).2 := by
  induction n using Nat.twoStepInduction with
  | zero => dsimp [Scheme.idealSheafPower]; infer_instance
  | one => dsimp [Scheme.idealSheafPower]; infer_instance
  | more n _ ih =>
    change Mono (Scheme.idealModuleProductι J.toModulesι
      (Scheme.idealSheafPower J.toModulesι (n + 1)).1 ≫
        (Scheme.idealSheafPower J.toModulesι (n + 1)).2)
    have := ih
    have : Mono (Scheme.idealModuleProductι J.toModulesι
        (Scheme.idealSheafPower J.toModulesι (n + 1)).1) := by
      dsimp [Scheme.idealModuleProductι]; infer_instance
    infer_instance

open CategoryTheory.Limits MonoidalCategory Opposite Scheme.Modules in
set_option backward.isDefEq.respectTransparency false in
/-- Compare the two ideal-power realizations using their equal affine ranges, then
factor through each other's inclusions by the cokernel universal property.
Source: Stacks, Schemes, Tags 01I8 and 01IC; Modules, Tags 01CE and 01AH. -/
private theorem power_inclusion_iso {X : Scheme.{v}} (J : X.IdealSheafData)
    (n : ℕ) (hn : 0 < n) :
    ∃ e : (Scheme.idealSheafPower J.toModulesι n).1 ≅ (J ^ n).toModules,
      e.hom ≫ (J ^ n).toModulesι = (Scheme.idealSheafPower J.toModulesι n).2 := by
  have := power_inclusion_mono J n
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have hr (U : X.affineOpens) :
      Set.range ((Scheme.idealSheafPower J.toModulesι n).2.app U.1) =
        Set.range ((J ^ n).toModulesι.app U.1) := by
    rw [(J ^ n).range_toModulesι_app]
    simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
    ext a
    exact Set.ext_iff.mp
      (((Scheme.Modules.ideal_times_quasiCoherent_affine_sections J
        (SheafOfModules.unit X.ringCatSheaf)).2.2.2.1 U).2.2.2 n hn) a
  have he : Subobject.mk (Scheme.idealSheafPower J.toModulesι n).2 =
      Subobject.mk (J ^ n).toModulesι := le_antisymm
    (Scheme.subobject_le_of_affine_range _ _ (fun U ↦ (hr U).subset))
    (Scheme.subobject_le_of_affine_range _ _ (fun U ↦ (hr U).symm.subset))
  exact ⟨Subobject.isoOfMkEqMk _ _ he, by simp⟩

open CategoryTheory.Limits MonoidalCategory Opposite Scheme.Modules in
set_option backward.isDefEq.respectTransparency false in
/-- Multiplication has zero image exactly when every ideal section kills every module
section. Check pure tensors using the sheafification adjunction.
Source: Stacks, Modules, Tag 01CD; adapted from `ClosedImmersionCoherentEquivalence`. -/
private theorem product_zero_iff {X : Scheme.{v}} (J : X.IdealSheafData)
    (F : X.Modules) :
    IsZero (Scheme.idealModuleProduct J.toModulesι F) ↔
      ∀ (V : X.Opens) (a : Γ(X, V)), a ∈ J.idealOfOpens V →
        ∀ s : Γ(F, V), a • s = 0 := by
  let μ : J.toModules ⊗ F ⟶ F := J.toModulesι ▷ F ≫ (λ_ F).hom
  have hm : IsZero (image μ) ↔ μ = 0 := by
    constructor
    · intro h
      exact eq_zero_of_image_eq_zero (h.eq_of_src _ _)
    · intro h
      have hi : image.ι μ = 0 := by
        apply (cancel_epi (factorThruImage μ)).mp
        simp only [image.fac, comp_zero, h]
      exact IsZero.of_mono_eq_zero (image.ι μ) hi
  change IsZero (image μ) ↔ _
  rw [hm]
  constructor
  · intro h V a ha s
    have hr : a ∈ Set.range (J.toModulesι.app V) := by
      rw [J.range_toModulesι_app_eq_idealOfOpens V]
      exact ha
    obtain ⟨b, rfl⟩ := hr
    have he := congrArg (fun f : J.toModules ⊗ F ⟶ F ↦ f.app V (tmulSection b s)) h
    dsimp only [μ] at he
    rw [Hom.comp_app, ConcreteCategory.comp_apply, whiskerRight_app_tmulSection] at he
    erw [leftUnitor_hom_app_tmulSection'] at he
    exact he
  · intro h
    let adj := sheafificationAdjunction X
    apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification J.toModules F).inv).mp
    apply (adj.homEquiv (J.toModules.val ⊗ F.val) F).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    apply PresheafOfModules.hom_ext
    intro U
    ext t
    change μ.val.app U
      ((SheafOfModules.tensorObjIsoSheafification J.toModules F).inv.val.app U
        (((adj.unit.app (J.toModules.val ⊗ F.val)).app U) t)) = _
    induction t using TensorProduct.inductionOn with
    | add t s ht hs => simp only [map_add, ht, hs]
    | tmul a s =>
      change μ.app U.unop (tmulSection a s) = 0
      dsimp only [μ]
      rw [Hom.comp_app, ConcreteCategory.comp_apply, whiskerRight_app_tmulSection]
      erw [leftUnitor_hom_app_tmulSection']
      exact h U.unop (J.toModulesι.app U.unop a)
        ((J.range_toModulesι_app_eq_idealOfOpens U.unop).subset ⟨a, rfl⟩) s

open CategoryTheory.Limits MonoidalCategory Opposite Scheme.Modules in
set_option backward.isDefEq.respectTransparency false in
/-- An isomorphism of ideal inclusions induces equality of the multiplication-image
subobjects and thus an isomorphism of the products respecting their inclusions. -/
private theorem product_inclusion_iso {X : Scheme.{v}} {A B : X.Modules}
    (a : A ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : B ⟶ SheafOfModules.unit X.ringCatSheaf)
    (e : A ≅ B) (he : e.hom ≫ b = a) (F : X.Modules) :
    ∃ d : Scheme.idealModuleProduct a F ≅ Scheme.idealModuleProduct b F,
      d.hom ≫ Scheme.idealModuleProductι b F = Scheme.idealModuleProductι a F := by
  have hm : (e.hom ▷ F) ≫ (b ▷ F ≫ (λ_ F).hom) = a ▷ F ≫ (λ_ F).hom := by
    rw [← comp_whiskerRight_assoc, he]
  have : Mono (Scheme.idealModuleProductι a F) := by
    dsimp [Scheme.idealModuleProductι]; infer_instance
  have : Mono (Scheme.idealModuleProductι b F) := by
    dsimp [Scheme.idealModuleProductι]; infer_instance
  have hs : Subobject.mk (Scheme.idealModuleProductι a F) =
      Subobject.mk (Scheme.idealModuleProductι b F) := by
    change imageSubobject (a ▷ F ≫ (λ_ F).hom) =
      imageSubobject (b ▷ F ≫ (λ_ F).hom)
    simpa only [hm] using
      imageSubobject_iso_comp (e.hom ▷ F) (b ▷ F ≫ (λ_ F).hom)
  exact ⟨Subobject.isoOfMkEqMk _ _ hs, by simp⟩

open CategoryTheory.Limits MonoidalCategory Opposite Scheme.Modules in
/-- Equality of ideal data transports its module inclusion. -/
private theorem ideal_inclusion_eq {X : Scheme.{v}} {J K : X.IdealSheafData}
    (h : J = K) :
    (eqToIso (congrArg Scheme.IdealSheafData.toModules h)).hom ≫ K.toModulesι =
      J.toModulesι := by
  subst K
  simp

open CategoryTheory.Limits MonoidalCategory Opposite Scheme.Modules in
set_option backward.isDefEq.respectTransparency false in
/-- Identify the power quotient with the closed pullback unit, then compare adjunctions.
The quotient projection equation specifies the isomorphism uniquely.
Source: Stacks, Morphisms of Spaces, Tag 04CJ (1), and Modules, Tag 08KS. -/
private theorem quotient_unit_power {Y Z : Scheme.{v}} (f : Z ⟶ Y)
    [IsClosedImmersion f] (J : Y.IdealSheafData) (n : ℕ) (hn : 0 < n)
    (hk : f.ker = J ^ n)
    (adj : Scheme.Modules.tensorPullback f ⊣ Scheme.Modules.pushforward f)
    (F : Y.Modules) :
    ∃ e : formalModuleQuotient J n F ≅
        (Scheme.Modules.pushforward f).obj ((Scheme.Modules.tensorPullback f).obj F),
      formalModuleQuotientπ J n F ≫ e.hom = adj.unit.app F := by
  obtain ⟨p₀, hp₀⟩ := power_inclusion_iso J n hn
  let p := p₀ ≪≫ eqToIso (congrArg Scheme.IdealSheafData.toModules hk.symm)
  have hp : p.hom ≫ f.ker.toModulesι = (Scheme.idealSheafPower J.toModulesι n).2 := by
    dsimp only [p, Iso.trans_hom]
    rw [Category.assoc, ideal_inclusion_eq hk.symm, hp₀]
  obtain ⟨d, hd⟩ := product_inclusion_iso _ _ p hp F
  let q := cokernel.mapIso (Scheme.idealModuleProductι
      (Scheme.idealSheafPower J.toModulesι n).2 F)
    (Scheme.idealModuleProductι f.ker.toModulesι F) d (Iso.refl F)
    (by simpa using hd.symm)
  have hq : formalModuleQuotientπ J n F ≫ q.hom =
      cokernel.π (Scheme.idealModuleProductι f.ker.toModulesι F) := by
    simp [q, formalModuleQuotientπ, cokernel.mapIso]
  obtain ⟨η, hη, _⟩ := Scheme.Modules.closedImmersion_unit_quotient f
  let adj₀ := Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction f)
  have hηF := hη F
  have : IsIso (η F) := hηF.2.2.2
  let c := adj₀.leftAdjointUniq adj
  refine ⟨q ≪≫ asIso (η F) ≪≫ (Scheme.Modules.pushforward f).mapIso (c.app F), ?_⟩
  change formalModuleQuotientπ J n F ≫ q.hom ≫ η F ≫
    (Scheme.Modules.pushforward f).map (c.app F).hom = _
  have hηeq : cokernel.π (Scheme.idealModuleProductι f.ker.toModulesι F) ≫ η F =
      adj₀.unit.app F := hηF.2.2.1
  rw [← Category.assoc, hq, ← Category.assoc, hηeq]
  exact Adjunction.unit_leftAdjointUniq_hom_app adj₀ adj F

/-- The explicit pushed system satisfies coherence, annihilation, and the quotient
transition condition. This is an object assertion, without full faithfulness or lifting.

Source: Stacks, Remark 088F, Lemma 087T, equation 0880
(blueprint: lem-weil-pbc-thickening-system-pushforward-adic).
Proof: Each `j n` is a closed immersion into a Noetherian scheme, so its source is
locally Noetherian. Finite pushforward preserves coherence; closed pushforward is
annihilated by its kernel `J^(n+1)`. On the affine basis the ideal-sheaf power and the
multiplication-image power have the same range. Factoring their monic inclusions through
each other gives an isomorphism respecting the inclusions. Tensoring with a module then
gives the same multiplication image, proving the annihilation conjunct. Since
`i n ≫ j (n+1) = j n` and both
projections are closed immersions, `i n` is a closed immersion with kernel
`(J^(n+1)).comap (j (n+1))`. The closed-immersion unit-quotient theorem, transported to
the supplied adjunction `ai n` by uniqueness of left adjoints, identifies the adjoint
of `M.comparison n` with the quotient projection followed by an isomorphism.
Push this identity along `j (n+1)`. Closed pushforward of ideal powers identifies its
source quotient with the quotient of the pushed term by `J^(n+1)`. Compose the quotient
comparison with the pushforward of `M.comparison n`, the pushforward-composition
comparison, and the comparison induced by `hi n`. This gives the required quotient
isomorphism. Its composite with the quotient projection is the explicit adjacent
transition. `Functor.ofOpSequence_map_homOfLE_succ` identifies this with the inverse
system's adjacent map. These are precisely the three defining conjuncts. -/
theorem thickeningSystemPushforward_isAdic
    {X : Scheme.{v}} [IsNoetherian X] {T : ℕ → Scheme.{v}}
    {i : ∀ n, T n ⟶ T (n + 1)}
    (j : ∀ n, T n ⟶ X) (hi : ∀ n, i n ≫ j (n + 1) = j n)
    (ai : ∀ n, Scheme.Modules.tensorPullback (i n) ⊣ Scheme.Modules.pushforward (i n))
    (J : X.IdealSheafData)
    (hgeom : ∀ n, IsClosedImmersion (j n) ∧ (j n).ker = J ^ (n + 1))
    (M : CoherentThickeningSystem T i) :
    IsCoherentFormalModule J ((thickeningSystemPushforward j hi ai).obj M) := by
  classical
  have hj (n : ℕ) : IsClosedImmersion (j n) := (hgeom n).1
  have hnoeth (n : ℕ) : IsLocallyNoetherian (T n) :=
    LocallyOfFiniteType.isLocallyNoetherian (j n)
  have hqc (n : ℕ) : (M.term n).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType (T n)
      (M.term n)).mp (M.coherent n)).1
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact (Scheme.Modules.isCoherent_pushforward_of_isFinite (j n)
      (M.term n) (M.coherent n)).1
  · intro n
    change CategoryTheory.Limits.IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower J.toModulesι (n + 1)).2
      ((Scheme.Modules.pushforward (j n)).obj (M.term n)))
    obtain ⟨e, he⟩ := power_inclusion_iso J (n + 1) (Nat.succ_pos n)
    obtain ⟨d, _⟩ := product_inclusion_iso _ _ e he
      ((Scheme.Modules.pushforward (j n)).obj (M.term n))
    apply CategoryTheory.Limits.IsZero.of_iso _ d
    apply (product_zero_iff (J ^ (n + 1)) _).mpr
    intro V a ha s
    have heq := congrArg (fun K : X.IdealSheafData ↦ K.idealOfOpens V) (hgeom n).2
    exact ((Scheme.Modules.closedImmersion_pushforward_annihilated (j n)).1
      (M.term n)).2 V a (heq.symm ▸ ha) s
  · intro n
    have hicomp : IsClosedImmersion (i n ≫ j (n + 1)) := hi n ▸ hj n
    have : IsClosedImmersion (i n) :=
      IsClosedImmersion.of_comp_isClosedImmersion (i n) (j (n + 1))
    have hk : (i n).ker = (J.comap (j (n + 1))) ^ (n + 1) := by
      rw [← Scheme.IdealSheafData.comap_map_of_isClosedImmersion (j (n + 1)) (i n).ker,
        Scheme.IdealSheafData.map_ker, hi n, (hgeom n).2,
        Scheme.IdealSheafData.comap_pow]
    obtain ⟨q, hq⟩ := quotient_unit_power (i n) (J.comap (j (n + 1)))
      (n + 1) (Nat.succ_pos n) hk (ai n) (M.term (n + 1))
    obtain ⟨ρ, hρ, _, _⟩ :=
      (Scheme.closedImmersion_pushforward_idealPowers (j (n + 1)) J).2.2.2
    let e := ρ (M.term (n + 1)) (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) ≪≫
      (Scheme.Modules.pushforward (j (n + 1))).mapIso q ≪≫
      (Scheme.Modules.pushforward (j (n + 1))).mapIso
        ((Scheme.Modules.pushforward (i n)).mapIso (M.comparison n)) ≪≫
      (thickeningPushforwardComparison j hi n).app (M.term n)
    refine ⟨e, ?_⟩
    change formalModuleQuotientπ J (n + 1)
      ((Scheme.Modules.pushforward (j (n + 1))).obj (M.term (n + 1))) ≫ e.hom = _
    rw [thickeningSystemPushforward_transition]
    dsimp only [e, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc,
      hρ (M.term (n + 1)) (n + 1) (Nat.succ_le_succ (Nat.zero_le n)),
      ← Functor.map_comp, hq]
    rw [← Functor.map_comp, ← Adjunction.homEquiv_unit]
    rfl

end
end AlgebraicGeometry
