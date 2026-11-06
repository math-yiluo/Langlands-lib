import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.TorsorCocycle
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Descent of local group isomorphisms with a trivial discrepancy cocycle -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S} {U : Over S}

/-- A group homomorphism over every point of a cover, natural on all test schemes. -/
structure LocalGroupHom (G H : GroupScheme S) (U : Over S) where
  toFun : ∀ {Z : Over S}, (Z ⟶ U) → ((Z ⟶ G.X) →* (Z ⟶ H.X))
  naturality : ∀ {Z Z' : Over S} (t : Z' ⟶ Z) (a : Z ⟶ U) (g : Z ⟶ G.X),
    toFun (t ≫ a) (t ≫ g) = t ≫ toFun a g

namespace LocalGroupHom

variable (e : LocalGroupHom G H U)

/-- The local homomorphisms agree for every pair of points of the cover. -/
def IsIndependent : Prop :=
  ∀ {Z : Over S} (a b : Z ⟶ U) (g : Z ⟶ G.X), e.toFun a g = e.toFun b g

private theorem underlying_rel {V Z Y : Over S} (p : V ⟶ Z) (f : V ⟶ Y)
    (hf : ∀ {W : Over S} (a b : W ⟶ V), a ≫ p = b ≫ p → a ≫ f = b ≫ f)
    {W : Scheme} (a b : W ⟶ V.left) (hab : a ≫ p.left = b ≫ p.left) :
    a ≫ f.left = b ≫ f.left := by
  have hb : b ≫ V.hom = a ≫ V.hom := by
    rw [← Over.w p, ← Category.assoc, ← Category.assoc, hab]
  let a₀ : Over.mk (a ≫ V.hom) ⟶ V := Over.homMk a rfl
  let b₀ : Over.mk (a ≫ V.hom) ⟶ V := Over.homMk b hb
  exact congrArg (fun q => q.left) (hf a₀ b₀ (Over.OverMorphism.ext hab))

private def overDesc {V Z Y : Over S} (p : V ⟶ Z) [EffectiveEpi p.left]
    (f : V ⟶ Y)
    (hf : ∀ {W : Over S} (a b : W ⟶ V), a ≫ p = b ≫ p → a ≫ f = b ≫ f) :
    Z ⟶ Y := by
  let d : Z.left ⟶ Y.left := EffectiveEpi.desc p.left f.left (underlying_rel p f hf)
  exact Over.homMk d (by
    apply (cancel_epi p.left).mp
    rw [← Category.assoc, show p.left ≫ d = f.left from EffectiveEpi.fac _ _ _,
      Over.w f, Over.w p])

private theorem overDesc_fac {V Z Y : Over S} (p : V ⟶ Z) [EffectiveEpi p.left]
    (f : V ⟶ Y)
    (hf : ∀ {W : Over S} (a b : W ⟶ V), a ≫ p = b ≫ p → a ≫ f = b ≫ f) :
    p ≫ overDesc p f hf = f := by
  apply Over.OverMorphism.ext
  change p.left ≫ EffectiveEpi.desc p.left f.left (underlying_rel p f hf) = f.left
  exact EffectiveEpi.fac p.left f.left (underlying_rel p f hf)

variable [QuasiCompact U.hom] [Flat U.hom] [Surjective U.hom]

private instance effectiveEpi_fst (Z : Over S) : EffectiveEpi (fst Z U).left := by
  change EffectiveEpi (CategoryTheory.Limits.pullback.fst Z.hom U.hom)
  infer_instance

variable (he : e.IsIndependent)

include he

omit [QuasiCompact U.hom] [Flat U.hom] [Surjective U.hom] in
private theorem local_rel (Z : Over S) (g : Z ⟶ G.X)
    {W : Over S} (a b : W ⟶ Z ⊗ U) (hab : a ≫ fst Z U = b ≫ fst Z U) :
    a ≫ e.toFun (snd Z U) (fst Z U ≫ g) =
      b ≫ e.toFun (snd Z U) (fst Z U ≫ g) := by
  rw [← e.naturality, ← e.naturality]
  simp only [← Category.assoc, hab]
  exact he _ _ _

/-- Descend the value of an independent local homomorphism at a group point. -/
def value {Z : Over S} (g : Z ⟶ G.X) : Z ⟶ H.X :=
  overDesc (fst Z U) (e.toFun (snd Z U) (fst Z U ≫ g)) (e.local_rel he Z g)

theorem value_fac {Z : Over S} (g : Z ⟶ G.X) :
    fst Z U ≫ e.value he g = e.toFun (snd Z U) (fst Z U ≫ g) :=
  overDesc_fac (fst Z U) (e.toFun (snd Z U) (fst Z U ≫ g)) (e.local_rel he Z g)

/-- Pulling a descended point to any test with a cover point recovers its local value. -/
theorem comp_value {Z W : Over S} (t : W ⟶ Z) (a : W ⟶ U) (g : Z ⟶ G.X) :
    t ≫ e.value he g = e.toFun a (t ≫ g) := by
  have h := congrArg (fun q => lift t a ≫ q) (e.value_fac he g)
  simpa only [← Category.assoc, lift_fst, ← e.naturality, lift_snd] using h

theorem value_naturality {Z W : Over S} (t : W ⟶ Z) (g : Z ⟶ G.X) :
    e.value he (t ≫ g) = t ≫ e.value he g := by
  apply Over.OverMorphism.ext
  apply (cancel_epi (fst W U).left).mp
  have h : fst W U ≫ e.value he (t ≫ g) = fst W U ≫ (t ≫ e.value he g) := by
    calc
      _ = e.toFun (snd W U) (fst W U ≫ (t ≫ g)) := e.value_fac he (t ≫ g)
      _ = e.toFun (snd W U) ((fst W U ≫ t) ≫ g) := by rw [Category.assoc]
      _ = (fst W U ≫ t) ≫ e.value he g :=
        (e.comp_value he (fst W U ≫ t) (snd W U) g).symm
      _ = _ := Category.assoc _ _ _
  exact congrArg (fun q => q.left) h

/-- The descended values preserve multiplication. -/
def pointsHom (Z : Over S) : (Z ⟶ G.X) →* (Z ⟶ H.X) where
  toFun := e.value he
  map_one' := by
    apply Over.OverMorphism.ext
    apply (cancel_epi (fst Z U).left).mp
    have h : fst Z U ≫ e.value he (1 : Z ⟶ G.X) = fst Z U ≫ (1 : Z ⟶ H.X) := by
      rw [e.value_fac, MonObj.comp_one, map_one, MonObj.comp_one]
    exact congrArg (fun q => q.left) h
  map_mul' g g' := by
    apply Over.OverMorphism.ext
    apply (cancel_epi (fst Z U).left).mp
    have h : fst Z U ≫ e.value he (g * g') =
        fst Z U ≫ (e.value he g * e.value he g') := by
      rw [e.value_fac, MonObj.comp_mul, map_mul, MonObj.comp_mul,
        e.value_fac, e.value_fac]
    exact congrArg (fun q => q.left) h

/-- An independent natural family descends to an actual group-scheme homomorphism. -/
def descend : G ⟶ H :=
  homOfPoints (e.pointsHom he) (e.value_naturality he)

@[simp] theorem comp_descend (Z : Over S) (g : Z ⟶ G.X) :
    g ≫ (e.descend he).hom.hom = e.value he g :=
  comp_homOfPoints (e.pointsHom he) (e.value_naturality he) Z g

end LocalGroupHom

/-- A group isomorphism over every point of a cover, natural on all test schemes. -/
structure LocalGroupIso (G H : GroupScheme S) (U : Over S) where
  toFun : ∀ {Z : Over S}, (Z ⟶ U) → ((Z ⟶ G.X) ≃* (Z ⟶ H.X))
  naturality : ∀ {Z Z' : Over S} (t : Z' ⟶ Z) (a : Z ⟶ U) (g : Z ⟶ G.X),
    toFun (t ≫ a) (t ≫ g) = t ≫ toFun a g

namespace LocalGroupIso

variable (e : LocalGroupIso G H U)

/-- Forget the inverse in each local isomorphism. -/
def toLocalGroupHom : LocalGroupHom G H U where
  toFun a := (e.toFun a).toMonoidHom
  naturality := e.naturality

/-- Inverting all local isomorphisms preserves naturality. -/
def symm : LocalGroupIso H G U where
  toFun a := (e.toFun a).symm
  naturality t a g := by
    apply (e.toFun (t ≫ a)).injective
    rw [MulEquiv.apply_symm_apply, e.naturality, MulEquiv.apply_symm_apply]

/-- Equality of the local maps for all pairs of points of the cover. -/
def IsIndependent : Prop := e.toLocalGroupHom.IsIndependent

theorem IsIndependent.symm (he : e.IsIndependent) : e.symm.IsIndependent := by
  intro Z a b g
  apply (e.toFun a).injective
  change e.toFun a ((e.toFun a).symm g) = e.toFun a ((e.toFun b).symm g)
  have h := he a b ((e.toFun b).symm g)
  change e.toFun a ((e.toFun b).symm g) = e.toFun b ((e.toFun b).symm g) at h
  rw [MulEquiv.apply_symm_apply, h, MulEquiv.apply_symm_apply]

/-- The given cocycle records the discrepancy between the local isomorphisms. -/
def HasDiscrepancy (a : AutomorphicAction A G) (ξ : Cocycle A U) : Prop :=
  ∀ {Z : Over S} (b c : Z ⟶ U) (g : Z ⟶ G.X),
    e.toFun b (a.act (ξ.toFun b c) g) = e.toFun c g

/-- Correct each local map by the action of the corresponding value of a cochain. -/
def twist (a : AutomorphicAction A G) (f : U ⟶ A.X) : LocalGroupIso G H U where
  toFun b := (a.pointAut _ (b ≫ f)).trans (e.toFun b)
  naturality t b g := by
    change e.toFun (t ≫ b) (a.act ((t ≫ b) ≫ f) (t ≫ g)) =
      t ≫ e.toFun b (a.act (b ≫ f) g)
    rw [Category.assoc, ← a.naturality, e.naturality]

/-- A cochain whose coboundary is the discrepancy makes the corrected maps agree. -/
theorem twist_isIndependent (a : AutomorphicAction A G) (ξ : Cocycle A U)
    (h : e.HasDiscrepancy a ξ) (f : U ⟶ A.X)
    (hf : ∀ {Z : Over S} (b c : Z ⟶ U), ξ.toFun b c = (b ≫ f) * (c ≫ f)⁻¹) :
    (e.twist a f).IsIndependent := by
  intro Z b c g
  change e.toFun b (a.act (b ≫ f) g) = e.toFun c (a.act (c ≫ f) g)
  have hc := h b c (a.act (c ≫ f) g)
  rw [hf, a.act_mul_left, a.act_inv_act] at hc
  exact hc

variable [QuasiCompact U.hom] [Flat U.hom] [Surjective U.hom]

private theorem descend_comp_symm (he : e.IsIndependent) :
    e.toLocalGroupHom.descend he ≫
      e.symm.toLocalGroupHom.descend (IsIndependent.symm e he) = 𝟙 G := by
  apply hom_ext_points
  intro Z g
  change g ≫ ((e.toLocalGroupHom.descend he).hom.hom ≫
      (e.symm.toLocalGroupHom.descend (IsIndependent.symm e he)).hom.hom) = g
  rw [← Category.assoc]
  rw [LocalGroupHom.comp_descend e.symm.toLocalGroupHom (IsIndependent.symm e he),
    LocalGroupHom.comp_descend e.toLocalGroupHom he]
  apply Over.OverMorphism.ext
  have : EffectiveEpi (fst Z U).left := by
    change EffectiveEpi (CategoryTheory.Limits.pullback.fst Z.hom U.hom)
    infer_instance
  apply (cancel_epi (fst Z U).left).mp
  have h : fst Z U ≫ e.symm.toLocalGroupHom.value (IsIndependent.symm e he)
      (e.toLocalGroupHom.value he g) = fst Z U ≫ g := by
    calc
      _ = (e.toFun (snd Z U)).symm (fst Z U ≫ e.toLocalGroupHom.value he g) :=
        e.symm.toLocalGroupHom.value_fac (IsIndependent.symm e he) _
      _ = (e.toFun (snd Z U)).symm (e.toFun (snd Z U) (fst Z U ≫ g)) :=
        congrArg (e.toFun (snd Z U)).symm (e.toLocalGroupHom.value_fac he g)
      _ = _ := MulEquiv.symm_apply_apply (e.toFun (snd Z U)) _
  exact congrArg (fun q => q.left) h

/-- An independent local isomorphism descends to a genuine group-scheme isomorphism. -/
def descend (he : e.IsIndependent) : G ≅ H where
  hom := e.toLocalGroupHom.descend he
  inv := e.symm.toLocalGroupHom.descend (IsIndependent.symm e he)
  hom_inv_id := e.descend_comp_symm he
  inv_hom_id := e.symm.descend_comp_symm (IsIndependent.symm e he)

/-- Triviality of an actual discrepancy cocycle descends the local group isomorphism. -/
def descendOfTrivial (a : AutomorphicAction A G) (ξ : Cocycle A U)
    (h : e.HasDiscrepancy a ξ) (hξ : ξ.IsTrivial) : G ≅ H :=
  (e.twist a hξ.choose).descend (e.twist_isIndependent a ξ h hξ.choose hξ.choose_spec)

end LocalGroupIso

end Langlands.GroupScheme
