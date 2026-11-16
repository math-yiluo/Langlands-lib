import Langlands.GroupScheme.Descent.PullHomCoherence
import Langlands.GroupScheme.Descent.DisjointComponentHoms

/-! # Direct pullback assembly on arbitrary disjoint components -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

namespace Langlands.GroupScheme.Descent

variable {S T U : Scheme.{u}}

/-- Direct pullback transport along the identity map changes no morphism. -/
@[simp] theorem pullHom_identity {f g : T ⟶ S} {G H : GroupScheme S}
    (a : (baseChange f).obj G ⟶ (baseChange g).obj H) :
    pullHom (𝟙 T) (Category.id_comp f) (Category.id_comp g) a = a := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have h := pullHom_eval (𝟙 T) (Category.id_comp f) (Category.id_comp g) a
      (pullback.fst G.X.hom f) (pullback.snd G.X.hom f) pullback.condition
    simpa only [pullback.lift_fst_snd, Category.id_comp, Category.comp_id] using h
  · exact (Over.w (pullHom (𝟙 T) (Category.id_comp f)
      (Category.id_comp g) a).hom.hom).trans (Over.w a.hom.hom).symm

/-- Direct pullback transport along the identity map changes no isomorphism. -/
@[simp] theorem pullIso_identity {f g : T ⟶ S} {G H : GroupScheme S}
    (a : (baseChange f).obj G ≅ (baseChange g).obj H) :
    pullIso (𝟙 T) (Category.id_comp f) (Category.id_comp g) a = a := by
  apply Iso.ext
  exact pullHom_identity a.hom

/-- Direct pullback transport respects composition of isomorphisms. -/
theorem pullIso_trans (q : U ⟶ T)
    {f g h : T ⟶ S} {r s t : U ⟶ S}
    (hf : q ≫ f = r) (hg : q ≫ g = s) (hh : q ≫ h = t)
    {G H K : GroupScheme S}
    (a : (baseChange f).obj G ≅ (baseChange g).obj H)
    (b : (baseChange g).obj H ≅ (baseChange h).obj K) :
    pullIso q hf hh (a ≪≫ b) = pullIso q hf hg a ≪≫ pullIso q hg hh b := by
  apply Iso.ext
  exact pullHom_comp q hf hg hh a.hom b.hom

namespace DisjointComponents

variable {I : Type u} {Z : I → Scheme.{u}}
    (q : ∀ i, Z i ⟶ T) [IsIso (Sigma.desc q)]
    {f g : T ⟶ S} {fi gi : ∀ i, Z i ⟶ S}
    (hf : ∀ i, q i ≫ f = fi i) (hg : ∀ i, q i ≫ g = gi i)
    {G H : GroupScheme S}

/-- Assemble actual isomorphisms with specified direct-pullback endpoints. -/
def pullbackIsoAlong
    (a : ∀ i, (baseChange (fi i)).obj G ≅ (baseChange (gi i)).obj H) :
    (baseChange f).obj G ≅ (baseChange g).obj H :=
  groupIso q (fun i =>
    pullbackComparison f (q i) (fi i) (hf i) G ≪≫ a i ≪≫
      (pullbackComparison g (q i) (gi i) (hg i) H).symm)

@[simp] theorem pullIso_pullbackIsoAlong
    (a : ∀ i, (baseChange (fi i)).obj G ≅ (baseChange (gi i)).obj H) (i : I) :
    pullIso (q i) (hf i) (hg i) (pullbackIsoAlong q hf hg a) = a i := by
  simp [pullIso, pullbackIsoAlong]

/-- Component restrictions with specified endpoints detect actual morphisms. -/
theorem pullHom_ext_along
    {a b : (baseChange f).obj G ⟶ (baseChange g).obj H}
    (h : ∀ i, pullHom (q i) (hf i) (hg i) a =
      pullHom (q i) (hf i) (hg i) b) : a = b := by
  apply groupHom_ext q
  intro i
  apply (cancel_epi (pullbackComparison f (q i) (fi i) (hf i) G).inv).mp
  apply (cancel_mono (pullbackComparison g (q i) (gi i) (hg i) H).hom).mp
  exact h i

/-- The corresponding extensionality principle for actual isomorphisms. -/
theorem pullIso_ext_along
    {a b : (baseChange f).obj G ≅ (baseChange g).obj H}
    (h : ∀ i, pullIso (q i) (hf i) (hg i) a =
      pullIso (q i) (hf i) (hg i) b) : a = b := by
  apply Iso.ext
  exact pullHom_ext_along q hf hg (fun i => congrArg Iso.hom (h i))

/-- Evaluate an assembled isomorphism along a map factoring through a component. -/
theorem pullIso_pullbackIsoAlong_factor
    (a : ∀ i, (baseChange (fi i)).obj G ≅ (baseChange (gi i)).obj H)
    (i : I) (v : U ⟶ Z i) {r : U ⟶ T} (hv : v ≫ q i = r)
    {f' g' : U ⟶ S} (hrf : r ≫ f = f') (hrg : r ≫ g = g') :
    pullIso r hrf hrg (pullbackIsoAlong q hf hg a) =
      pullIso v
        (by rw [← hf i, ← Category.assoc, hv]; exact hrf)
        (by rw [← hg i, ← Category.assoc, hv]; exact hrg) (a i) := by
  subst r
  rw [← pullIso_pullIso (q i) v (hf i) (hg i), pullIso_pullbackIsoAlong]

end DisjointComponents

namespace CoproductComponents

variable {I : Type u} {X : I → Scheme.{u}} (a : T ⟶ ∐ X)

/-- The inverse image of one actual coproduct component. -/
abbrev piece (i : I) : Scheme.{u} := pullback a (Sigma.ι X i)

/-- Inclusion of a component inverse image into the test scheme. -/
abbrev toBase (i : I) : piece a i ⟶ T := pullback.fst a (Sigma.ι X i)

/-- The map from a component inverse image to that component. -/
abbrev toComponent (i : I) : piece a i ⟶ X i := pullback.snd a (Sigma.ι X i)

@[reassoc (attr := simp)] theorem component_condition (i : I) :
    toComponent a i ≫ Sigma.ι X i = toBase a i ≫ a := pullback.condition.symm

/-- The inverse images form an arbitrary disjoint decomposition of the test scheme. -/
instance pieces_isIso : IsIso (Sigma.desc (toBase a)) := by
  have hι : IsIso (Sigma.desc (fun i => Sigma.ι X i)) := by
    simpa only [Sigma.desc_ι] using (inferInstance : IsIso (𝟙 (∐ X)))
  exact DisjointComponents.projection_isIso (fun i => Sigma.ι X i) (Over.mk a)

/-- Factor a test map through a component inverse image using its given coordinate. -/
def lift (i : I) (q : U ⟶ T) (g : U ⟶ X i)
    (h : g ≫ Sigma.ι X i = q ≫ a) : U ⟶ piece a i :=
  pullback.lift q g h.symm

@[reassoc (attr := simp)] theorem lift_toBase (i : I) (q : U ⟶ T)
    (g : U ⟶ X i) (h : g ≫ Sigma.ι X i = q ≫ a) :
    lift a i q g h ≫ toBase a i = q := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem lift_toComponent (i : I) (q : U ⟶ T)
    (g : U ⟶ X i) (h : g ≫ Sigma.ι X i = q ≫ a) :
    lift a i q g h ≫ toComponent a i = g := pullback.lift_snd _ _ _

end CoproductComponents

end Langlands.GroupScheme.Descent
