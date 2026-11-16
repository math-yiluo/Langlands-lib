import Langlands.GroupScheme.AutomorphicAction.LocallyInner
import Langlands.AbelianScheme.KernelBaseChange

/-! # Transport and composition of fppf-locally inner automorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {A G : GroupScheme S} (a : AutomorphicAction A G)

/-- The identity point represents the identity automorphism. -/
theorem representsIso_one {T : Over S} :
    a.RepresentsIso (Iso.refl G) (1 : T ⟶ A.X) := by
  intro W t g
  simp only [MonObj.comp_one, a.act_one_left, Iso.refl_hom, Grp.id_hom_hom,
    Category.comp_id]

/-- Inverting a representative represents the inverse automorphism. -/
theorem RepresentsIso.inv {σ : G ≅ G} {T : Over S} {x : T ⟶ A.X}
    (hx : a.RepresentsIso σ x) : a.RepresentsIso σ.symm x⁻¹ := by
  intro W t g
  have he := hx t (g ≫ σ.inv.hom.hom)
  have hi : (g ≫ σ.inv.hom.hom) ≫ σ.hom.hom.hom = g := by
    rw [Category.assoc, ← Grp.comp_hom_hom, σ.inv_hom_id, Grp.id_hom_hom,
      Category.comp_id]
  rw [hi] at he
  change a.act (t ≫ x⁻¹) g = g ≫ σ.inv.hom.hom
  rw [GrpObj.comp_inv]
  calc
    a.act (t ≫ x)⁻¹ g =
        a.act (t ≫ x)⁻¹ (a.act (t ≫ x) (g ≫ σ.inv.hom.hom)) :=
      congrArg (a.act (t ≫ x)⁻¹) he.symm
    _ = g ≫ σ.inv.hom.hom := a.act_inv_act _ _

/-- Multiplying representatives in action order represents their composition. -/
theorem RepresentsIso.trans {σ τ : G ≅ G} {T : Over S} {x y : T ⟶ A.X}
    (hx : a.RepresentsIso σ x) (hy : a.RepresentsIso τ y) :
    a.RepresentsIso (σ ≪≫ τ) (y * x) := by
  intro W t g
  rw [MonObj.comp_mul, a.act_mul_left, hx t g, hy t (g ≫ σ.hom.hom.hom)]
  rfl

end Langlands.GroupScheme.AutomorphicAction

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- The identity automorphism is fppf-locally inner. -/
theorem IsFppfLocallyInner.refl (G : GroupScheme S) :
    IsFppfLocallyInner (Iso.refl G) :=
  ⟨Over.mk (𝟙 S), (by change Flat (𝟙 S); infer_instance),
    (by change Surjective (𝟙 S); infer_instance),
    (by change LocallyOfFinitePresentation (𝟙 S); infer_instance), 1,
    (AutomorphicAction.conjugation (𝟙 G)).representsIso_one⟩

/-- Fppf-local innerness is closed under inversion. -/
theorem IsFppfLocallyInner.symm {σ : G ≅ G} (hσ : IsFppfLocallyInner σ) :
    IsFppfLocallyInner σ.symm := by
  obtain ⟨V, hf, hs, hl, x, hx⟩ := hσ
  exact ⟨V, hf, hs, hl, x⁻¹, hx.inv _⟩

/-- A common fppf refinement composes two locally inner automorphisms. -/
theorem IsFppfLocallyInner.trans {σ τ : G ≅ G}
    (hσ : IsFppfLocallyInner σ) (hτ : IsFppfLocallyInner τ) :
    IsFppfLocallyInner (σ ≪≫ τ) := by
  obtain ⟨V, hf, hs, hl, x, hx⟩ := hσ
  obtain ⟨U, kf, ks, kl, y, hy⟩ := hτ
  let : Flat V.hom := hf
  let : Surjective V.hom := hs
  let : LocallyOfFinitePresentation V.hom := hl
  let : Flat U.hom := kf
  let : Surjective U.hom := ks
  let : LocallyOfFinitePresentation U.hom := kl
  let Z : Over S := Over.mk (pullback.fst V.hom U.hom ≫ V.hom)
  let r : Z ⟶ V := Over.homMk (pullback.fst V.hom U.hom) rfl
  let s : Z ⟶ U := Over.homMk (pullback.snd V.hom U.hom) pullback.condition.symm
  refine ⟨Z, ?_, ?_, ?_, (s ≫ y) * (r ≫ x), ?_⟩
  · dsimp [Z]
    infer_instance
  · dsimp [Z]
    infer_instance
  · dsimp [Z]
    infer_instance
  · exact AutomorphicAction.RepresentsIso.trans _ (hx.comp _ r) (hy.comp _ s)

/-- Transport through any actual group-scheme isomorphism preserves local
innerness, with the local conjugator transported by the same isomorphism. -/
theorem IsFppfLocallyInner.transport {σ : G ≅ G} (hσ : IsFppfLocallyInner σ)
    (e : G ≅ H) : IsFppfLocallyInner (e.symm ≪≫ σ ≪≫ e) := by
  obtain ⟨V, hf, hs, hl, x, hx⟩ := hσ
  refine ⟨V, hf, hs, hl, x ≫ e.hom.hom.hom, ?_⟩
  intro W t g
  have he := congrArg (fun z => z ≫ e.hom.hom.hom)
    (hx t (g ≫ e.inv.hom.hom))
  simp only [AutomorphicAction.conjugation_act, Grp.id_hom_hom,
    Category.comp_id] at he ⊢
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp] at he
  have hi : (g ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = g := by
    rw [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom,
      Category.comp_id]
  rw [hi] at he
  change (t ≫ (x ≫ e.hom.hom.hom)) * g * (t ≫ (x ≫ e.hom.hom.hom))⁻¹ =
    ((g ≫ e.inv.hom.hom) ≫ σ.hom.hom.hom) ≫ e.hom.hom.hom
  simpa only [Category.assoc] using he

/-- Pulling back the witness cover and conjugator preserves local innerness. -/
theorem IsFppfLocallyInner.baseChange {S' : Scheme.{u}} {σ : G ≅ G}
    (hσ : IsFppfLocallyInner σ) (b : S' ⟶ S) :
    IsFppfLocallyInner ((GroupScheme.baseChange b).mapIso σ) := by
  obtain ⟨V, hf, hs, hl, x, hx⟩ := hσ
  let : Flat V.hom := hf
  let : Surjective V.hom := hs
  let : LocallyOfFinitePresentation V.hom := hl
  let V' : Over S' := (Over.pullback b).obj V
  let r : (Over.map b).obj V' ⟶ V :=
    Over.homMk (pullback.fst V.hom b) pullback.condition
  let y : V' ⟶ ((GroupScheme.baseChange b).obj G).X :=
    (baseChangePointsEquiv b G V').symm (r ≫ x)
  refine ⟨V', ?_, ?_, ?_, y, ?_⟩
  · change Flat (pullback.snd V.hom b)
    infer_instance
  · change Surjective (pullback.snd V.hom b)
    infer_instance
  · change LocallyOfFinitePresentation (pullback.snd V.hom b)
    infer_instance
  · intro W t g
    simp only [AutomorphicAction.conjugation_act, Grp.id_hom_hom,
      Category.comp_id]
    apply (baseChangePointsEquiv b G W).injective
    change _ = baseChangePointsEquiv b G W
      (g ≫ ((Over.pullback b).mapGrp.map σ.hom).hom.hom)
    rw [baseChangePointsEquiv_comp b σ.hom W g]
    simp only [map_mul, map_inv,
      baseChangePointsEquiv_naturality, y, MulEquiv.apply_symm_apply]
    simpa only [AutomorphicAction.conjugation_act, Grp.id_hom_hom,
      Category.comp_id, Category.assoc] using
      hx ((Over.map b).map t ≫ r) (baseChangePointsEquiv b G W g)

/-- Two actual comparisons have the same outer class when their discrepancy
is fppf-locally inner on their source. -/
def IsFppfInnerEquivalent (e d : G ≅ H) : Prop :=
  IsFppfLocallyInner (e ≪≫ d.symm)

namespace IsFppfInnerEquivalent

variable {J K : GroupScheme S}

/-- Every comparison is inner-equivalent to itself. -/
theorem refl (e : G ≅ H) : IsFppfInnerEquivalent e e := by
  simpa only [IsFppfInnerEquivalent, Iso.self_symm_id] using
    IsFppfLocallyInner.refl G

/-- Inner equivalence is symmetric. -/
theorem symm {e d : G ≅ H} (h : IsFppfInnerEquivalent e d) :
    IsFppfInnerEquivalent d e := by
  change IsFppfLocallyInner (e ≪≫ d.symm) at h
  simpa only [IsFppfInnerEquivalent, Iso.trans_symm, Iso.symm_symm_eq] using h.symm

/-- Inner equivalence is transitive. -/
theorem trans {e d k : G ≅ H}
    (h : IsFppfInnerEquivalent e d) (h' : IsFppfInnerEquivalent d k) :
    IsFppfInnerEquivalent e k := by
  change IsFppfLocallyInner (e ≪≫ d.symm) at h
  change IsFppfLocallyInner (d ≪≫ k.symm) at h'
  simpa only [IsFppfInnerEquivalent, Iso.trans_assoc, Iso.symm_self_id_assoc]
    using h.trans h'

/-- Precomposing both comparisons transports their discrepancy. -/
theorem precomp {e d : G ≅ H} (h : IsFppfInnerEquivalent e d) (f : J ≅ G) :
    IsFppfInnerEquivalent (f ≪≫ e) (f ≪≫ d) := by
  change IsFppfLocallyInner (e ≪≫ d.symm) at h
  simpa only [IsFppfInnerEquivalent, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
    using h.transport f.symm

/-- Postcomposing both comparisons leaves their source discrepancy unchanged. -/
theorem postcomp {e d : G ≅ H} (h : IsFppfInnerEquivalent e d) (f : H ≅ K) :
    IsFppfInnerEquivalent (e ≪≫ f) (d ≪≫ f) := by
  simpa only [IsFppfInnerEquivalent, Iso.trans_symm, Iso.trans_assoc,
    Iso.self_symm_id_assoc] using h

/-- Composition respects inner equivalence in both comparisons. -/
theorem comp {e d : G ≅ H} {k l : H ≅ K}
    (h : IsFppfInnerEquivalent e d) (h' : IsFppfInnerEquivalent k l) :
    IsFppfInnerEquivalent (e ≪≫ k) (d ≪≫ l) :=
  (h.postcomp k).trans (h'.precomp d)

/-- Inverting both comparisons preserves inner equivalence. -/
theorem inv {e d : G ≅ H} (h : IsFppfInnerEquivalent e d) :
    IsFppfInnerEquivalent e.symm d.symm := by
  change IsFppfLocallyInner (e ≪≫ d.symm) at h
  simpa only [IsFppfInnerEquivalent, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl] using h.symm.transport e

/-- Arbitrary base change preserves inner equivalence. -/
theorem baseChange {S' : Scheme.{u}} {e d : G ≅ H}
    (h : IsFppfInnerEquivalent e d) (b : S' ⟶ S) :
    IsFppfInnerEquivalent ((GroupScheme.baseChange b).mapIso e)
      ((GroupScheme.baseChange b).mapIso d) := by
  change IsFppfLocallyInner (e ≪≫ d.symm) at h
  simpa only [IsFppfInnerEquivalent, Functor.mapIso_trans, Functor.mapIso_symm]
    using h.baseChange b

end IsFppfInnerEquivalent

end Langlands.GroupScheme
