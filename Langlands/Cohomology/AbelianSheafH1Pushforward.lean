import Langlands.Cohomology.CechPullback
import Langlands.AlgebraicGeometry.Picard.UnitSheafPushforwardNaturality
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Homeomorphism compatibility of the actual Čech-to-H¹ comparison -/

noncomputable section

universe w u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Langlands.Cohomology.AbelianSheafH1Pushforward

open Cech AbelianSheafCechH1 AbelianSheafH1Naturality
open Langlands.AlgebraicGeometry.Picard.UnitSheafPushforward

set_option backward.isDefEq.respectTransparency false

section Cochains

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  {P Q : TopCat.Presheaf AddCommGrpCat.{u} X}
  {ι : Type w} (U : ι → Opens Y)

/-- The preimage of a full family is full. -/
lemma preimage_fullCover (hcov : ⊤ ≤ iSup U) :
    ⊤ ≤ ⨆ i, (Opens.map f).obj (U i) := by
  intro x _
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcov (show f x ∈ (⊤ : Opens Y) from trivial))
  exact Opens.mem_iSup.2 ⟨i, hi⟩

/-- Preimage cochain transport commutes with a coefficient morphism. -/
lemma cochains_map (φ : P ⟶ Q) (p : ℕ)
    (z : C ((Opens.map f).op ⋙ P) U p) :
    CechPullback.cochains f Q U p
        (map U (Functor.whiskerLeft (Opens.map f).op φ) p z) =
      map (fun i => (Opens.map f).obj (U i)) φ p
        (CechPullback.cochains f P U p z) := by
  funext σ
  exact (map_res φ (CechPullback.inter_preimage f U σ).le (z σ)).symm

/-- The section itself is unchanged when transporting its degree-zero cochain. -/
lemma cochains_globalCochain (s : P.obj (op ⊤)) :
    CechPullback.cochains f P U 0 (globalCochain ((Opens.map f).op ⋙ P) U s) =
      globalCochain P (fun i => (Opens.map f).obj (U i)) s := by
  funext σ
  change res (P := P) _ (res (P := P) _ s) = res (P := P) _ s
  rw [res_res]

end Cochains

local instance {X Y : TopCat.{u}} (f : X ⟶ Y)
    (S : ShortComplex (X.Sheaf AddCommGrpCat.{u}))
    [TopCat.Presheaf.IsFlasque S.X₂.1] :
    TopCat.Presheaf.IsFlasque
      (S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)).X₂.1 :=
  TopCat.Sheaf.IsFlasque.pushforward_isFlasque S.X₂ f

section Representatives

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  {ι : Type w} {U : ι → Opens Y}
  {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}

/-- Transport a pushed short-complex representative to the preimage family. -/
def transportRepresentative
    {z : C ((Opens.map f).op ⋙ S.X₁.1) U 1}
    (r : Representative
      (S := S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)) z) :
    Representative (S := S) (CechPullback.cochains f S.X₁.1 U 1 z) where
  primitive := CechPullback.cochains f S.X₂.1 U 0 r.primitive
  quotientSection := r.quotientSection
  primitive_d := by
    have hr :
        d ((Opens.map f).op ⋙ S.X₂.1) U 0 r.primitive =
          map U (Functor.whiskerLeft (Opens.map f).op S.f.hom) 1 z :=
      r.primitive_d
    rw [CechPullback.d_cochains, hr, cochains_map]
  quotient := by
    have hr :
        map U (Functor.whiskerLeft (Opens.map f).op S.g.hom) 0 r.primitive =
          globalCochain ((Opens.map f).op ⋙ S.X₃.1) U r.quotientSection :=
      r.quotient
    rw [← cochains_map, hr, cochains_globalCochain]

variable (e : X ≅ Y)

local instance :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).IsEquivalence :=
  (sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) e).isEquivalence_functor

/-- Transport identifies the actual connecting classes of the representatives. -/
lemma transportRepresentative_value (hS : S.ShortExact)
    {z : C ((Opens.map e.hom).op ⋙ S.X₁.1) U 1}
    (r : Representative
      (S := S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom)) z) :
    (transportRepresentative e.hom r).value hS =
      cohomologyPushforwardEquiv e S.X₁ 1
        (r.value (hS.map_of_exact
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom))) := by
  unfold Representative.value
  rw [cohomologyPushforwardEquiv_δ e hS]
  exact congrArg (Sheaf.H.δ hS 0 1 rfl)
    (cohomologyPushforwardEquiv_equiv₀_symm e S.X₃ r.quotientSection).symm

end Representatives

section Quotients

variable {X Y : TopCat.{u}} (e : X ≅ Y)
  {ι : Type w} [Finite ι] (U : ι → Opens Y)

local instance :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).IsEquivalence :=
  (sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) e).isEquivalence_functor

variable {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
  [TopCat.Presheaf.IsFlasque S.X₂.1]

/-- The finite-cover quotient comparison commutes with homeomorphism pushforward. -/
theorem quotientClassHom_pushforward (hS : S.ShortExact) (hcov : ⊤ ≤ iSup U)
    (x : CechH1 ((Opens.map e.hom).op ⋙ S.X₁.1) U) :
    quotientClassHom hS (preimage_fullCover e.hom U hcov)
        (CechPullback.h1Equiv e.hom S.X₁.1 U x) =
      cohomologyPushforwardEquiv e S.X₁ 1
        (quotientClassHom
          (hS.map_of_exact (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom)) hcov x) := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    rw [CechPullback.h1Equiv_mk, quotientClassHom_mk, quotientClassHom_mk]
    let r := chosenRepresentative
      (S := S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom)) hcov z
    rw [cocycleClassHom_eq_value hS _ _ (transportRepresentative e.hom r),
      cocycleClassHom_eq_value
        (hS.map_of_exact (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom)) hcov z r]
    exact transportRepresentative_value e hS r

end Quotients

section Comparison

variable {X Y : TopCat.{u}} (e : X ≅ Y)

local instance :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).IsEquivalence :=
  (sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) e).isEquivalence_functor

local instance {T : TopCat.{u}} (F : T.Sheaf AddCommGrpCat.{u}) :
    TopCat.Sheaf.IsFlasque (Injective.under F) :=
  AbelianSheafFlasque.isFlasque_of_injective (Injective.under F)

/-- Compare the chosen embedding after pushforward with the pushed chosen embedding. -/
def injectiveScPushforwardMap (F : X.Sheaf AddCommGrpCat.{u}) :
    AbelianSheafFlasque.injectiveSc
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F) ⟶
      (AbelianSheafFlasque.injectiveSc F).map
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom) := by
  let ψ := Injective.factorThru
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).map (Injective.ι F))
    (Injective.ι ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F))
  have hψ : Injective.ι ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F) ≫ ψ =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).map (Injective.ι F) :=
    Injective.comp_factorThru _ _
  have hz : Injective.ι ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F) ≫
      (ψ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).map
        (cokernel.π (Injective.ι F))) = 0 := by
    rw [← Category.assoc, hψ, ← Functor.map_comp, cokernel.condition, Functor.map_zero]
  exact
    { τ₁ := 𝟙 _
      τ₂ := ψ
      τ₃ := cokernel.desc _ _ hz
      comm₁₂ := by
        change 𝟙 _ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).map
          (Injective.ι F) = Injective.ι _ ≫ ψ
        simpa only [Category.id_comp] using hψ.symm
      comm₂₃ := (cokernel.π_desc _ _ _).symm }

@[simp]
lemma injectiveScPushforwardMap_τ₁ (F : X.Sheaf AddCommGrpCat.{u}) :
    (injectiveScPushforwardMap e F).τ₁ = 𝟙 _ := rfl

variable {ι : Type w} [Finite ι] (U : ι → Opens Y)

/-- The pushed injective sequence computes the same chosen comparison on the pushed sheaf. -/
lemma quotientClassHom_pushedInjective (F : X.Sheaf AddCommGrpCat.{u})
    (hcov : ⊤ ≤ iSup U)
    (x : CechH1 ((Opens.map e.hom).op ⋙ F.1) U) :
    quotientClassHom
        ((AbelianSheafFlasque.injectiveSc_shortExact F).map_of_exact
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom)) hcov x =
      comparisonHom ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F) U hcov x := by
  have h := quotientClassHom_naturality
    (AbelianSheafFlasque.injectiveSc_shortExact
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F))
    ((AbelianSheafFlasque.injectiveSc_shortExact F).map_of_exact
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom))
    (injectiveScPushforwardMap e F) hcov x
  change quotientClassHom
      ((AbelianSheafFlasque.injectiveSc_shortExact F).map_of_exact
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom)) hcov
      (mapHom U (𝟙 ((Opens.map e.hom).op ⋙ F.1)) x) =
    Sheaf.H.map (𝟙 ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F)) 1
      (comparisonHom ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F)
        U hcov x) at h
  rw [show mapHom U (𝟙 ((Opens.map e.hom).op ⋙ F.1)) x = x from mapHom_id U x] at h
  exact h.trans (Sheaf.H.map_id_apply _)

/-- The actual Čech-to-H¹ comparison commutes with the published homeomorphism equivalence. -/
theorem comparisonHom_pushforward (F : X.Sheaf AddCommGrpCat.{u})
    (hcov : ⊤ ≤ iSup U)
    (x : CechH1 ((Opens.map e.hom).op ⋙ F.1) U) :
    comparisonHom F (fun i => (Opens.map e.hom).obj (U i))
        (preimage_fullCover e.hom U hcov)
        (CechPullback.h1Equiv e.hom F.1 U x) =
      cohomologyPushforwardEquiv e F 1
        (comparisonHom ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F)
          U hcov x) := by
  exact (quotientClassHom_pushforward e U
    (AbelianSheafFlasque.injectiveSc_shortExact F) hcov x).trans
      (congrArg (cohomologyPushforwardEquiv e F 1)
        (quotientClassHom_pushedInjective e U F hcov x))

end Comparison

end Langlands.Cohomology.AbelianSheafH1Pushforward
