import Langlands.GroupScheme.HomScheme.ClosedEmbeddingModel
import Langlands.GroupScheme.HomScheme.ConjugationMap
import Langlands.AlgebraicGeometry.FiniteFreeSchemeActionRelation

/-! # Free source-automorphism actions on closed-embedding schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.HomScheme.ClosedEmbeddingModel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable {S : Scheme.{u}} {H G : GroupScheme S} (M : ClosedEmbeddingModel H G)

/-- Precompose the universal embedding by an actual source isomorphism. -/
def precompose (e : H ≅ H) : M.scheme ⟶ M.scheme :=
  M.parameter ((GroupScheme.baseChange M.scheme.hom).map e.hom ≫ M.family)
    ((IsClosedSubgroup.of_iso ((GroupScheme.baseChange M.scheme.hom).mapIso e)).comp M.closed)

private theorem evaluate_hom_comp {A B C : GroupScheme S} {T T' : Over S}
    (a : T' ⟶ T) (f : RelativeHom A B T) (g : RelativeHom B C T) :
    evaluate a (f ≫ g) = evaluate a f ≫ evaluate a g :=
  Descent.pullHom_comp a.left (Over.w a) (Over.w a) (Over.w a) f g

/-- Precomposition on parameters has the expected evaluation on all tests. -/
theorem evaluate_precompose (e : H ≅ H) {T : Over S} (a : T ⟶ M.scheme) :
    evaluate (a ≫ M.precompose e) M.family =
      (GroupScheme.baseChange T.hom).map e.hom ≫ evaluate a M.family := by
  rw [evaluate_comp]
  unfold precompose
  rw [evaluate_parameter, evaluate_hom_comp, evaluate_baseChange]

@[simp]
theorem precompose_refl : M.precompose (Iso.refl H) = 𝟙 M.scheme := by
  apply M.parameter_ext
  have h := M.evaluate_precompose (Iso.refl H) (𝟙 M.scheme)
  have hid : (GroupScheme.baseChange M.scheme.hom).map (Iso.refl H).hom = 𝟙 _ :=
    (GroupScheme.baseChange M.scheme.hom).map_id H
  rw [hid] at h
  simpa only [Category.id_comp, evaluate_id] using h

/-- Precomposition reverses the order of source-isomorphism composition. -/
theorem precompose_comp (e f : H ≅ H) :
    M.precompose e ≫ M.precompose f = M.precompose (f ≪≫ e) := by
  apply M.parameter_ext
  rw [evaluate_precompose]
  have h₁ := M.evaluate_precompose e (𝟙 M.scheme)
  have h₂ := M.evaluate_precompose (f ≪≫ e) (𝟙 M.scheme)
  simp only [Category.id_comp, evaluate_id] at h₁ h₂
  rw [h₁, h₂, Iso.trans_hom, Functor.map_comp, Category.assoc]

/-- The parameter automorphism defined by a source automorphism. -/
def precompositionIso (e : H ≅ H) : M.scheme ≅ M.scheme where
  hom := M.precompose e
  inv := M.precompose e.symm
  hom_inv_id := by rw [precompose_comp, Iso.symm_self_id, precompose_refl]
  inv_hom_id := by rw [precompose_comp, Iso.self_symm_id, precompose_refl]

/-- Faithful actions on the source act freely on all closed embeddings. The
source isomorphisms are indexed in the order opposite to their composition. -/
def precompositionAction {K : Type u} [Group K] (α : K → (H ≅ H))
    (h1 : (α 1).hom = 𝟙 H)
    (hmul : ∀ g h, (α (g * h)).hom = (α h).hom ≫ (α g).hom)
    (hfaithful : ∀ (T : Over S) [Nonempty T.left],
      Function.Injective (fun k => (GroupScheme.baseChange T.hom).map (α k).hom)) :
    Langlands.AlgebraicGeometry.FiniteFreeSchemeAction K M.scheme.left where
  act k := (Over.forget S).mapIso (M.precompositionIso (α k))
  one := by
    have he : α 1 = Iso.refl H := Iso.ext h1
    change (M.precompose (α 1)).left = 𝟙 _
    rw [he, precompose_refl]
    rfl
  mul g h := by
    have he : α (g * h) = α h ≪≫ α g := Iso.ext (hmul g h)
    change (M.precompose (α g)).left ≫ (M.precompose (α h)).left =
      (M.precompose (α (g * h))).left
    rw [he]
    exact congrArg Over.Hom.left (M.precompose_comp (α g) (α h))
  free {T} hT a := by
    let : Nonempty T := hT
    intro g h hgh
    let T' : Over S := Over.mk (a ≫ M.scheme.hom)
    let : Nonempty T'.left := hT
    let a' : T' ⟶ M.scheme := Over.homMk a rfl
    have hparams : a' ≫ M.precompose (α g) = a' ≫ M.precompose (α h) :=
      Over.OverMorphism.ext hgh
    have heval := congrArg (fun p => evaluate p M.family) hparams
    rw [evaluate_precompose, evaluate_precompose] at heval
    let F := evaluate a' M.family
    let : IsClosedImmersion F.hom.hom.left := isClosedImmersion_evaluate a' M.family M.closed
    have hmaps : (GroupScheme.baseChange T'.hom).map (α g).hom =
        (GroupScheme.baseChange T'.hom).map (α h).hom := by
      apply Grp.hom_ext
      apply Over.OverMorphism.ext
      apply (cancel_mono F.hom.hom.left).mp
      exact congrArg (fun f => f.hom.hom.left) heval
    exact hfaithful T' hmaps

/-- The action maps preserve the original base scheme. -/
theorem precompositionAction_over {K : Type u} [Group K] (α : K → (H ≅ H))
    (h1 : (α 1).hom = 𝟙 H)
    (hmul : ∀ g h, (α (g * h)).hom = (α h).hom ≫ (α g).hom)
    (hfaithful : ∀ (T : Over S) [Nonempty T.left],
      Function.Injective (fun k => (GroupScheme.baseChange T.hom).map (α k).hom)) (k : K) :
    ((M.precompositionAction α h1 hmul hfaithful).act k).hom ≫ M.scheme.hom = M.scheme.hom :=
  Over.w (M.precompose (α k))

/-- Conjugation of a closed embedding remains a closed embedding on every test. -/
theorem isClosed_conjugationFamily (f : H ⟶ G) (hf : IsClosedSubgroup f)
    {T : Over S} (g : T ⟶ G.X) : IsClosedSubgroup (conjugationFamily f g) :=
  (hf.baseChange T.hom).comp_iso
    (((GroupScheme.baseChange T.hom).obj G).innerIso (RelativeLevi.pulledBackPoint G T g))

/-- The conjugation map into the actual closed-embedding parameter scheme. -/
def conjugationMap (f : H ⟶ G) (hf : IsClosedSubgroup f) : G.X ⟶ M.scheme :=
  M.parameter (conjugationFamily f (𝟙 G.X)) (isClosed_conjugationFamily f hf _)

/-- Every test-valued point evaluates the conjugation map to its actual family. -/
theorem evaluate_conjugationMap (f : H ⟶ G) (hf : IsClosedSubgroup f)
    {T : Over S} (g : T ⟶ G.X) :
    evaluate (g ≫ M.conjugationMap f hf) M.family = conjugationFamily f g := by
  rw [evaluate_comp]
  unfold conjugationMap
  rw [evaluate_parameter, evaluate_conjugationFamily, Category.comp_id]

end Langlands.GroupScheme.HomScheme.ClosedEmbeddingModel
