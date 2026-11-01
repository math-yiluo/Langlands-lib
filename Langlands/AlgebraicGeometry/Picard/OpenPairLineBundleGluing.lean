import Langlands.AlgebraicGeometry.Modules.OpenPairModuleGluing
import Langlands.AlgebraicGeometry.Picard.LineBundleOpenCoverGluing

/-! # Binary gluing of actual line bundles and open unions -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.OpenPairLineBundleGluing

open Langlands.Scheme.Modules (squarePullbackIso)
open Langlands.Scheme.Modules.OpenPairModuleGluing

variable {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X)
  [IsOpenImmersion f] [IsOpenImmersion g] (L : LineBundle Y) (K : LineBundle Z)
  (φ : (Scheme.Modules.pullback (pullback.fst f g)).obj L.obj ≅
    (Scheme.Modules.pullback (pullback.snd f g)).obj K.obj)

/-- Joint coverage makes the compatible-pair module locally free of rank one. -/
lemma glued_rankOne (hcover : ∀ x : X, x ∈ f.opensRange ∨ x ∈ g.opensRange) :
    IsLocallyFreeRankOne (glued f g L.obj K.obj φ) := by
  intro x
  rcases hcover x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · exact IsLocallyFreeRankOne.exists_of_pullback f
      (L.property.of_iso (leftIso f g L.obj K.obj φ).symm) y
  · exact IsLocallyFreeRankOne.exists_of_pullback g
      (K.property.of_iso (rightIso f g L.obj K.obj φ).symm) z

/-- The actual line bundle glued from two jointly covering open immersions. -/
def glue (hcover : ∀ x : X, x ∈ f.opensRange ∨ x ∈ g.opensRange) : LineBundle X :=
  ⟨glued f g L.obj K.obj φ, glued_rankOne f g L K φ hcover⟩

/-- Its actual pullback to the left chart is the prescribed left bundle. -/
def leftModuleIso (hcover : ∀ x : X, x ∈ f.opensRange ∨ x ∈ g.opensRange) :
    (Scheme.Modules.pullback f).obj (glue f g L K φ hcover).obj ≅ L.obj :=
  leftIso f g L.obj K.obj φ

/-- Its actual pullback to the right chart is the prescribed right bundle. -/
def rightModuleIso (hcover : ∀ x : X, x ∈ f.opensRange ∨ x ∈ g.opensRange) :
    (Scheme.Modules.pullback g).obj (glue f g L K φ hcover).obj ≅ K.obj :=
  rightIso f g L.obj K.obj φ

/-- The gluing comparisons realize precisely the prescribed overlap identification. -/
lemma compatible (hcover : ∀ x : X, x ∈ f.opensRange ∨ x ∈ g.opensRange) :
    (Scheme.Modules.pullback (pullback.fst f g)).map
        (leftModuleIso f g L K φ hcover).hom ≫ φ.hom =
      (squarePullbackIso g (pullback.fst f g) (pullback.snd f g) f pullback.condition
        (glue f g L K φ hcover).obj).hom ≫
          (Scheme.Modules.pullback (pullback.snd f g)).map
            (rightModuleIso f g L K φ hcover).hom :=
  Langlands.Scheme.Modules.OpenPairModuleGluing.compatible f g L.obj K.obj φ

end Langlands.AlgebraicGeometry.Picard.OpenPairLineBundleGluing

namespace Langlands.AlgebraicGeometry.Picard.OpenUnion

variable {X Y Z : Scheme.{u}}

/-- Factor a scheme morphism through an open containing its image. -/
def lift (f : Y ⟶ X) (O : X.Opens) (hf : Set.range f ⊆ O) : Y ⟶ O.toScheme :=
  IsOpenImmersion.lift O.ι f (by simpa only [Scheme.Opens.range_ι] using hf)

@[reassoc (attr := simp)]
lemma lift_ι (f : Y ⟶ X) (O : X.Opens) (hf : Set.range f ⊆ O) :
    lift f O hf ≫ O.ι = f :=
  IsOpenImmersion.lift_fac _ _ _

instance (f : Y ⟶ X) [IsOpenImmersion f] (O : X.Opens) (hf : Set.range f ⊆ O) :
    IsOpenImmersion (lift f O hf) := by
  have : IsOpenImmersion (lift f O hf ≫ O.ι) := by rw [lift_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ O.ι

/-- The two original open immersions factored through the union of their images. -/
def left (f : Y ⟶ X) (g : Z ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g] :
    Y ⟶ (f.opensRange ⊔ g.opensRange).toScheme :=
  lift f _ (fun _ hx ↦ Or.inl hx)

def right (f : Y ⟶ X) (g : Z ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g] :
    Z ⟶ (f.opensRange ⊔ g.opensRange).toScheme :=
  lift g _ (fun _ hx ↦ Or.inr hx)

instance (f : Y ⟶ X) (g : Z ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g] :
    IsOpenImmersion (left f g) := by
  unfold left
  infer_instance

instance (f : Y ⟶ X) (g : Z ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g] :
    IsOpenImmersion (right f g) := by
  unfold right
  infer_instance

@[reassoc (attr := simp)]
lemma left_ι (f : Y ⟶ X) (g : Z ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g] :
    left f g ≫ (f.opensRange ⊔ g.opensRange).ι = f :=
  lift_ι f _ _

@[reassoc (attr := simp)]
lemma right_ι (f : Y ⟶ X) (g : Z ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g] :
    right f g ≫ (f.opensRange ⊔ g.opensRange).ι = g :=
  lift_ι g _ _

/-- Factoring through an open subscheme preserves the actual scheme overlap. -/
def overlapIso (f : Y ⟶ X) (g : Z ⟶ X) (O : X.Opens)
    (hf : Set.range f ⊆ O) (hg : Set.range g ⊆ O) :
    pullback (lift f O hf) (lift g O hg) ≅ pullback f g where
  hom := pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
    simpa only [Category.assoc, lift_ι] using
      congrArg (fun k ↦ k ≫ O.ι) (pullback.condition (f := lift f O hf) (g := lift g O hg)))
  inv := pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
    apply (cancel_mono O.ι).1
    simpa only [Category.assoc, lift_ι] using (pullback.condition (f := f) (g := g)))
  hom_inv_id := by apply pullback.hom_ext <;> simp
  inv_hom_id := by apply pullback.hom_ext <;> simp

@[reassoc (attr := simp)]
lemma overlapIso_hom_fst (f : Y ⟶ X) (g : Z ⟶ X) (O : X.Opens)
    (hf : Set.range f ⊆ O) (hg : Set.range g ⊆ O) :
    (overlapIso f g O hf hg).hom ≫ pullback.fst f g =
      pullback.fst (lift f O hf) (lift g O hg) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma overlapIso_hom_snd (f : Y ⟶ X) (g : Z ⟶ X) (O : X.Opens)
    (hf : Set.range f ⊆ O) (hg : Set.range g ⊆ O) :
    (overlapIso f g O hf hg).hom ≫ pullback.snd f g =
      pullback.snd (lift f O hf) (lift g O hg) :=
  pullback.lift_snd _ _ _

/-- Transport an ambient overlap identification to the overlap over a containing open. -/
def overlap (f : Y ⟶ X) (g : Z ⟶ X) (O : X.Opens)
    (hf : Set.range f ⊆ O) (hg : Set.range g ⊆ O)
    (M : Y.Modules) (N : Z.Modules)
    (φ : (Scheme.Modules.pullback (pullback.fst f g)).obj M ≅
      (Scheme.Modules.pullback (pullback.snd f g)).obj N) :
    (Scheme.Modules.pullback (pullback.fst (lift f O hf) (lift g O hg))).obj M ≅
      (Scheme.Modules.pullback (pullback.snd (lift f O hf) (lift g O hg))).obj N :=
  (Langlands.Scheme.Modules.compIso (overlapIso f g O hf hg).hom _ _
    (overlapIso_hom_fst f g O hf hg) M).symm ≪≫
      (Scheme.Modules.pullback (overlapIso f g O hf hg).hom).mapIso φ ≪≫
        Langlands.Scheme.Modules.compIso (overlapIso f g O hf hg).hom _ _
          (overlapIso_hom_snd f g O hf hg) N

/-- These two factors jointly cover the open union. -/
lemma cover (f : Y ⟶ X) (g : Z ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (x : (f.opensRange ⊔ g.opensRange).toScheme) :
    x ∈ (left f g).opensRange ∨ x ∈ (right f g).opensRange := by
  rcases x.2 with ⟨y, hy⟩ | ⟨z, hz⟩
  · left
    refine ⟨y, ?_⟩
    apply Subtype.ext
    change ((left f g ≫ (f.opensRange ⊔ g.opensRange).ι) y) = x.1
    exact (congrArg (fun k : Y ⟶ X ↦ k y) (lift_ι f _ _)).trans hy
  · right
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change ((right f g ≫ (f.opensRange ⊔ g.opensRange).ι) z) = x.1
    exact (congrArg (fun k : Z ⟶ X ↦ k z) (lift_ι g _ _)).trans hz

/-- An actual line bundle on the union, starting with an ambient overlap identification. -/
def glue (f : Y ⟶ X) (g : Z ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (L : LineBundle Y) (K : LineBundle Z)
    (φ : (Scheme.Modules.pullback (pullback.fst f g)).obj L.obj ≅
      (Scheme.Modules.pullback (pullback.snd f g)).obj K.obj) :
    LineBundle (f.opensRange ⊔ g.opensRange).toScheme :=
  OpenPairLineBundleGluing.glue (left f g) (right f g) L K
    (overlap f g _ (fun _ hx ↦ Or.inl hx) (fun _ hx ↦ Or.inr hx) L.obj K.obj φ)
    (cover f g)

/-- Actual left-chart pullback comparison for gluing on a union. -/
def leftModuleIso (f : Y ⟶ X) (g : Z ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (L : LineBundle Y) (K : LineBundle Z)
    (φ : (Scheme.Modules.pullback (pullback.fst f g)).obj L.obj ≅
      (Scheme.Modules.pullback (pullback.snd f g)).obj K.obj) :
    (Scheme.Modules.pullback (left f g)).obj (glue f g L K φ).obj ≅ L.obj :=
  OpenPairLineBundleGluing.leftModuleIso _ _ _ _ _ _

/-- Actual right-chart pullback comparison for gluing on a union. -/
def rightModuleIso (f : Y ⟶ X) (g : Z ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (L : LineBundle Y) (K : LineBundle Z)
    (φ : (Scheme.Modules.pullback (pullback.fst f g)).obj L.obj ≅
      (Scheme.Modules.pullback (pullback.snd f g)).obj K.obj) :
    (Scheme.Modules.pullback (right f g)).obj (glue f g L K φ).obj ≅ K.obj :=
  OpenPairLineBundleGluing.rightModuleIso _ _ _ _ _ _

/-- The union comparisons realize the transported ambient overlap identification. -/
lemma compatible (f : Y ⟶ X) (g : Z ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (L : LineBundle Y) (K : LineBundle Z)
    (φ : (Scheme.Modules.pullback (pullback.fst f g)).obj L.obj ≅
      (Scheme.Modules.pullback (pullback.snd f g)).obj K.obj) :
    (Scheme.Modules.pullback (pullback.fst (left f g) (right f g))).map
        (leftModuleIso f g L K φ).hom ≫
      (overlap f g _ (fun _ hx ↦ Or.inl hx) (fun _ hx ↦ Or.inr hx) L.obj K.obj φ).hom =
    (Langlands.Scheme.Modules.squarePullbackIso (right f g)
      (pullback.fst (left f g) (right f g)) (pullback.snd (left f g) (right f g))
      (left f g) pullback.condition (glue f g L K φ).obj).hom ≫
        (Scheme.Modules.pullback (pullback.snd (left f g) (right f g))).map
          (rightModuleIso f g L K φ).hom :=
  OpenPairLineBundleGluing.compatible _ _ _ _ _ _

end Langlands.AlgebraicGeometry.Picard.OpenUnion
