import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralDescentStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralRigidityStatement
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.Descent.FpqcHomDescent
import Langlands.AbelianScheme.KernelBaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Descent of central homomorphisms from rigidity (SGA 3, IX, 5.4 from 5.3) -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme.MultiplicativeTypeCentralDescent

/-! ### The quotient of two central homomorphisms -/

section Difference

variable {Y : Scheme.{u}} {A B : GroupScheme Y}

/-- Postcomposition with an isomorphism preserves centrality. -/
theorem isCentral_comp_iso {i : A ⟶ B} (hi : IsCentral i) {B' : GroupScheme Y} (e : B ≅ B') :
    IsCentral (i ≫ e.hom) := by
  intro T x T' a h
  have hc := hi T x T' a (h ≫ e.inv.hom.hom)
  have he : h = (h ≫ e.inv.hom.hom) ≫ e.hom.hom.hom := by
    rw [Category.assoc]
    change h = h ≫ (e.inv ≫ e.hom).hom.hom
    rw [Iso.inv_hom_id]
    rfl
  change Commute (a ≫ x ≫ i.hom.hom ≫ e.hom.hom.hom) h
  rw [he]
  simp only [← Category.assoc]
  change (((a ≫ x) ≫ i.hom.hom) ≫ e.hom.hom.hom) * ((h ≫ e.inv.hom.hom) ≫ e.hom.hom.hom) =
    ((h ≫ e.inv.hom.hom) ≫ e.hom.hom.hom) * (((a ≫ x) ≫ i.hom.hom) ≫ e.hom.hom.hom)
  rw [← MonObj.mul_comp, ← MonObj.mul_comp]
  congr 1

variable (f g : A ⟶ B)

/-- The pointwise quotient `f · g⁻¹` of two central homomorphisms is a homomorphism. -/
theorem isMonHom_mul_inv (hf : IsCentral f) (hg : IsCentral g) :
    IsMonHom (f.hom.hom * g.hom.hom⁻¹) where
  one_hom := by
    rw [MonObj.one_eq_one, MonObj.one_eq_one, MonObj.comp_mul, GrpObj.comp_inv,
      MonObj.one_comp, MonObj.one_comp, inv_one, mul_one]
  mul_hom := by
    rw [MonObj.mul_eq_mul, MonObj.mul_eq_mul, MonObj.comp_mul, MonObj.comp_mul,
      GrpObj.comp_inv, MonObj.mul_comp, MonObj.mul_comp,
      CartesianMonoidalCategory.tensorHom_fst, CartesianMonoidalCategory.tensorHom_snd,
      MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, GrpObj.comp_inv]
    set a := CartesianMonoidalCategory.fst A.X A.X ≫ f.hom.hom
    set b := CartesianMonoidalCategory.fst A.X A.X ≫ g.hom.hom
    set c := CartesianMonoidalCategory.snd A.X A.X ≫ f.hom.hom
    set d := CartesianMonoidalCategory.snd A.X A.X ≫ g.hom.hom
    have hc : ∀ z, Commute c z := commute_of_mem_center (hf _ _)
    have hd : ∀ z, Commute d z := commute_of_mem_center (hg _ _)
    have key : Commute (c * d⁻¹) b⁻¹ := (hc b⁻¹).mul_left (hd b⁻¹).inv_left
    calc a * c * (b * d)⁻¹ = a * ((c * d⁻¹) * b⁻¹) := by group
      _ = a * (b⁻¹ * (c * d⁻¹)) := by rw [key.eq]
      _ = a * b⁻¹ * (c * d⁻¹) := by group

/-- The homomorphism `f · g⁻¹` for central `f` and `g`. -/
def diffHom (hf : IsCentral f) (hg : IsCentral g) : A ⟶ B :=
  letI := isMonHom_mul_inv f g hf hg
  Grp.homMk (f.hom.hom * g.hom.hom⁻¹)

/-- The base change of `f · g⁻¹` along `q` is trivial exactly when `f` and `g` agree on the
pullback of `A` along `q`. -/
theorem baseChange_diffHom_eq_one_iff (hf : IsCentral f) (hg : IsCentral g)
    {T : Scheme.{u}} (q : T ⟶ Y) :
    ((GroupScheme.baseChange q).map (diffHom f g hf hg)).hom.hom = 1 ↔
      pullback.fst A.X.hom q ≫ f.hom.hom.left = pullback.fst A.X.hom q ≫ g.hom.hom.left := by
  let P := ((GroupScheme.baseChange q).obj A).X
  let c := baseChangePointsEquiv q A P (𝟙 P)
  have hcl : c.left = pullback.fst A.X.hom q := by
    change (baseChangePointsEquiv q A P (𝟙 P)).left = _
    rw [baseChangePointsEquiv_left]
    exact Category.id_comp _
  have hw : baseChangePointsEquiv q B P
      ((GroupScheme.baseChange q).map (diffHom f g hf hg)).hom.hom =
        c ≫ (diffHom f g hf hg).hom.hom := by
    have := baseChangePointsEquiv_comp q (diffHom f g hf hg) P (𝟙 P)
    rwa [Category.id_comp] at this
  rw [← (baseChangePointsEquiv q B P).map_eq_one_iff, hw]
  change c ≫ (f.hom.hom * g.hom.hom⁻¹) = 1 ↔ _
  rw [MonObj.comp_mul, GrpObj.comp_inv, mul_inv_eq_one, ← hcl]
  constructor
  · intro h
    exact congrArg (fun z => z.left) h
  · intro h
    exact Over.OverMorphism.ext h

end Difference

/-! ### Agreement over a morphism, tested on points -/

section Agreement

variable {X Y W T : Scheme.{u}} (p : X ⟶ Y) (q : T ⟶ Y) (φ ψ : X ⟶ W)

/-- Agreement after pulling back along `q`, phrased on points. -/
theorem fst_comp_eq_iff :
    pullback.fst p q ≫ φ = pullback.fst p q ≫ ψ ↔
      ∀ (Z : Scheme.{u}) (α : Z ⟶ X) (β : Z ⟶ T), α ≫ p = β ≫ q → α ≫ φ = α ≫ ψ := by
  constructor
  · intro h Z α β hαβ
    have := congrArg (fun k => pullback.lift α β hαβ ≫ k) h
    simpa only [pullback.lift_fst_assoc] using this
  · intro h
    exact h _ _ _ pullback.condition

/-- Agreement over `r ≫ q` for a flat surjective `r` implies agreement over `q`. -/
theorem agree_of_flat_comp {T' : Scheme.{u}} (r : T' ⟶ T) [Flat r] [Surjective r]
    (h : ∀ (Z : Scheme.{u}) (α : Z ⟶ X) (β : Z ⟶ T'), α ≫ p = β ≫ r ≫ q → α ≫ φ = α ≫ ψ) :
    ∀ (Z : Scheme.{u}) (α : Z ⟶ X) (β : Z ⟶ T), α ≫ p = β ≫ q → α ≫ φ = α ≫ ψ := by
  intro Z α β hαβ
  have : Epi (pullback.fst β r) := Flat.epi_of_flat_of_surjective _
  apply (cancel_epi (pullback.fst β r)).mp
  have := h _ (pullback.fst β r ≫ α) (pullback.snd β r) (by
    rw [Category.assoc, hαβ, ← Category.assoc, pullback.condition, Category.assoc])
  simpa only [Category.assoc] using this

end Agreement

/-! ### The two pullbacks of `u'` to the double overlap -/

section Overlap

variable {S S' : Scheme.{u}} (π : S' ⟶ S) {H G : GroupScheme S}
variable (u' : (GroupScheme.baseChange π).obj H ⟶ (GroupScheme.baseChange π).obj G)

open Descent

/-- The pullback of `u'` along the first projection `S' ×_S S' ⟶ S'`. -/
abbrev u₁ : (GroupScheme.baseChange (fst π)).obj ((GroupScheme.baseChange π).obj H) ⟶
    (GroupScheme.baseChange (fst π)).obj ((GroupScheme.baseChange π).obj G) :=
  (GroupScheme.baseChange (fst π)).map u'

/-- The pullback of `u'` along the second projection, transported to the first pullback by the
canonical identifications. -/
abbrev u₂ : (GroupScheme.baseChange (fst π)).obj ((GroupScheme.baseChange π).obj H) ⟶
    (GroupScheme.baseChange (fst π)).obj ((GroupScheme.baseChange π).obj G) :=
  (canonicalOverlap π H).hom ≫ (GroupScheme.baseChange (snd π)).map u' ≫
    (canonicalOverlap π G).inv

theorem isCentral_u₁ (hu : IsCentral u') : IsCentral (u₁ π u') :=
  hu.baseChange _

theorem isCentral_u₂ (hu : IsCentral u') : IsCentral (u₂ π u') := by
  have h1 := (hu.baseChange (snd π)).comp (canonicalOverlap π H).hom
  have h2 := isCentral_comp_iso h1 (canonicalOverlap π G).symm
  simpa only [Iso.symm_hom, Category.assoc] using h2

@[reassoc] theorem baseChange_map_fst {T U : Scheme.{u}} (q : T ⟶ U)
    {C D : GroupScheme U} (a : C ⟶ D) :
    ((GroupScheme.baseChange q).map a).hom.hom.left ≫ pullback.fst D.X.hom q =
      pullback.fst C.X.hom q ≫ a.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- The canonical overlap identification keeps the `H`-coordinate. -/
@[reassoc] theorem canonical_fst_fst (C : GroupScheme S) :
    (canonicalOverlap π C).hom.hom.hom.left ≫
        pullback.fst ((GroupScheme.baseChange π).obj C).X.hom (snd π) ≫
          pullback.fst C.X.hom π =
      pullback.fst ((GroupScheme.baseChange π).obj C).X.hom (fst π) ≫
        pullback.fst C.X.hom π :=
  canonicalOverlap_fst π C

/-- The inverse canonical overlap identification keeps the original coordinate. -/
@[reassoc] theorem canonical_inv_fst_fst (C : GroupScheme S) :
    (canonicalOverlap π C).inv.hom.hom.left ≫
        pullback.fst ((GroupScheme.baseChange π).obj C).X.hom (fst π) ≫
          pullback.fst C.X.hom π =
      pullback.fst ((GroupScheme.baseChange π).obj C).X.hom (snd π) ≫
        pullback.fst C.X.hom π := by
  have hid : (canonicalOverlap π C).inv.hom.hom.left ≫
      (canonicalOverlap π C).hom.hom.hom.left = 𝟙 _ := by
    exact congrArg (fun k => k.hom.hom.left) (Iso.inv_hom_id (canonicalOverlap π C))
  rw [← canonical_fst_fst π C, reassoc_of% hid]

/-- The canonical overlap identification sends the `S'`-coordinate to the second
projection. -/
@[reassoc] theorem canonical_fst_snd (C : GroupScheme S) :
    (canonicalOverlap π C).hom.hom.hom.left ≫
        pullback.fst ((GroupScheme.baseChange π).obj C).X.hom (snd π) ≫
          pullback.snd C.X.hom π =
      ((GroupScheme.baseChange (fst π)).obj ((GroupScheme.baseChange π).obj C)).X.hom ≫
        snd π := by
  have hw := Over.w (canonicalOverlap π C).hom.hom.hom
  change (canonicalOverlap π C).hom.hom.hom.left ≫
    pullback.snd ((GroupScheme.baseChange π).obj C).X.hom (snd π) =
    pullback.snd ((GroupScheme.baseChange π).obj C).X.hom (fst π) at hw
  change (canonicalOverlap π C).hom.hom.hom.left ≫
      pullback.fst ((GroupScheme.baseChange π).obj C).X.hom (snd π) ≫
        ((GroupScheme.baseChange π).obj C).X.hom = _
  rw [pullback.condition, reassoc_of% hw]
  rfl

/-- The first projection of the first pullback has `S'`-coordinate the first projection. -/
@[reassoc] theorem fst_snd (C : GroupScheme S) :
    pullback.fst ((GroupScheme.baseChange π).obj C).X.hom (fst π) ≫
        pullback.snd C.X.hom π =
      ((GroupScheme.baseChange (fst π)).obj ((GroupScheme.baseChange π).obj C)).X.hom ≫
        fst π :=
  pullback.condition

@[reassoc] theorem u₁_fst_fst :
    (u₁ π u').hom.hom.left ≫
        pullback.fst ((GroupScheme.baseChange π).obj G).X.hom (fst π) ≫
          pullback.fst G.X.hom π =
      pullback.fst ((GroupScheme.baseChange π).obj H).X.hom (fst π) ≫
        u'.hom.hom.left ≫ pullback.fst G.X.hom π := by
  rw [baseChange_map_fst_assoc]

@[reassoc] theorem u₂_fst_fst :
    (u₂ π u').hom.hom.left ≫
        pullback.fst ((GroupScheme.baseChange π).obj G).X.hom (fst π) ≫
          pullback.fst G.X.hom π =
      (canonicalOverlap π H).hom.hom.hom.left ≫
        pullback.fst ((GroupScheme.baseChange π).obj H).X.hom (snd π) ≫
          u'.hom.hom.left ≫ pullback.fst G.X.hom π := by
  change ((canonicalOverlap π H).hom.hom.hom.left ≫
      ((GroupScheme.baseChange (snd π)).map u').hom.hom.left ≫
        (canonicalOverlap π G).inv.hom.hom.left) ≫ _ = _
  simp only [Category.assoc, canonical_inv_fst_fst, baseChange_map_fst_assoc]

/-- Maps into the first pullback of `G` are determined by their original and base
coordinates. -/
theorem hom_ext_B {Z : Scheme.{u}}
    (φ ψ : Z ⟶ ((GroupScheme.baseChange (fst π)).obj ((GroupScheme.baseChange π).obj G)).X.left)
    (h₁ : φ ≫ pullback.fst ((GroupScheme.baseChange π).obj G).X.hom (fst π) ≫
        pullback.fst G.X.hom π =
      ψ ≫ pullback.fst ((GroupScheme.baseChange π).obj G).X.hom (fst π) ≫
        pullback.fst G.X.hom π)
    (h₂ : φ ≫ ((GroupScheme.baseChange (fst π)).obj
        ((GroupScheme.baseChange π).obj G)).X.hom =
      ψ ≫ ((GroupScheme.baseChange (fst π)).obj ((GroupScheme.baseChange π).obj G)).X.hom) :
    φ = ψ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using h₁
    · simp only [Category.assoc, fst_snd]
      rw [← Category.assoc, h₂, Category.assoc]
  · exact h₂

/-- Over the diagonal, the two pullbacks of `u'` agree. -/
theorem agree_diagonal :
    ∀ (Z : Scheme.{u})
      (α : Z ⟶ ((GroupScheme.baseChange (fst π)).obj ((GroupScheme.baseChange π).obj H)).X.left)
      (β : Z ⟶ S'),
      α ≫ ((GroupScheme.baseChange (fst π)).obj ((GroupScheme.baseChange π).obj H)).X.hom =
          β ≫ pullback.diagonal π →
        α ≫ (u₁ π u').hom.hom.left = α ≫ (u₂ π u').hom.hom.left := by
  intro Z α β hαβ
  have hx : α ≫ pullback.fst ((GroupScheme.baseChange π).obj H).X.hom (fst π) =
      α ≫ (canonicalOverlap π H).hom.hom.hom.left ≫
        pullback.fst ((GroupScheme.baseChange π).obj H).X.hom (snd π) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, canonical_fst_fst]
    · simp only [Category.assoc, canonical_fst_snd, fst_snd]
      rw [reassoc_of% hαβ, reassoc_of% hαβ]
      simp
  apply hom_ext_B π
  · simp only [Category.assoc, u₁_fst_fst, u₂_fst_fst]
    rw [← Category.assoc, hx]
    simp only [Category.assoc]
  · have w₁ := Over.w (u₁ π u').hom.hom
    have w₂ := Over.w (u₂ π u').hom.hom
    simp only [Category.assoc]
    rw [w₁, w₂]

/-- If the two pullbacks of `u'` agree, then `u'` is constant on the fibres of
`H' ⟶ H`. -/
theorem constant_of_eq
    (h : (u₁ π u').hom.hom.left = (u₂ π u').hom.hom.left) :
    ∀ (Z : Scheme.{u}) (x y : Z ⟶ pullback H.X.hom π),
      x ≫ pullback.fst H.X.hom π = y ≫ pullback.fst H.X.hom π →
        x ≫ u'.hom.hom.left ≫ pullback.fst G.X.hom π =
          y ≫ u'.hom.hom.left ≫ pullback.fst G.X.hom π := by
  intro Z x y hxy
  have hcond : (x ≫ pullback.snd H.X.hom π) ≫ π = (y ≫ pullback.snd H.X.hom π) ≫ π := by
    simp only [Category.assoc, ← pullback.condition]
    rw [← Category.assoc, hxy, Category.assoc]
  let α : Z ⟶ ((GroupScheme.baseChange (fst π)).obj
      ((GroupScheme.baseChange π).obj H)).X.left :=
    pullback.lift x (pullback.lift (x ≫ pullback.snd H.X.hom π)
      (y ≫ pullback.snd H.X.hom π) hcond) (by
        change x ≫ pullback.snd H.X.hom π = _
        simp)
  have hα₁ : α ≫ pullback.fst ((GroupScheme.baseChange π).obj H).X.hom (fst π) = x :=
    pullback.lift_fst _ _ _
  have hα₂ : α ≫ (canonicalOverlap π H).hom.hom.hom.left ≫
      pullback.fst ((GroupScheme.baseChange π).obj H).X.hom (snd π) = y := by
    apply pullback.hom_ext
    · simp only [Category.assoc, canonical_fst_fst]
      rw [← Category.assoc, hα₁, hxy]
    · simp only [Category.assoc, canonical_fst_snd]
      change (α ≫ pullback.snd _ _) ≫ snd π = _
      simp [α]
  have := congrArg (fun k => α ≫ k ≫
    pullback.fst ((GroupScheme.baseChange π).obj G).X.hom (fst π) ≫
      pullback.fst G.X.hom π) h
  simp only [u₁_fst_fst, u₂_fst_fst] at this
  rw [← hα₁, ← hα₂]
  simpa only [Category.assoc] using this

end Overlap

/-! ### Clopen subsets of the double overlap containing the diagonal -/

section Connected

variable {S S' : Scheme.{u}} (π : S' ⟶ S)

/-- If the geometric fibres of `π` are connected, a clopen subset of `S' ×_S S'` containing
the diagonal is everything. -/
theorem mem_of_isClopen_of_diagonal
    (hconn : ∀ (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ S),
      ConnectedSpace ↥(pullback π x))
    (U : Set ↥(pullback π π)) (hU : IsClopen U)
    (hdiag : ∀ y : S', pullback.diagonal π y ∈ U) (t : ↥(pullback π π)) : t ∈ U := by
  let κ := (pullback π π).residueField t
  let K := AlgebraicClosure κ
  let τ : Spec (CommRingCat.of K) ⟶ pullback π π :=
    Spec.map (CommRingCat.ofHom (algebraMap κ K)) ≫ (pullback π π).fromSpecResidueField t
  let a := τ ≫ pullback.fst π π
  let b := τ ≫ pullback.snd π π
  let x := a ≫ π
  have hb : b ≫ π = x := by
    simp only [b, x, a, Category.assoc, pullback.condition]
  have := hconn K x
  let m : pullback π x ⟶ pullback π π :=
    pullback.lift (pullback.fst π x) (pullback.snd π x ≫ b) (by
      rw [pullback.condition, Category.assoc, hb])
  let σa : Spec (CommRingCat.of K) ⟶ pullback π x :=
    pullback.lift a (𝟙 _) (by simp [x])
  let σb : Spec (CommRingCat.of K) ⟶ pullback π x :=
    pullback.lift b (𝟙 _) (by simp [hb])
  have hma : σa ≫ m = τ := by
    apply pullback.hom_ext
    · simp [m, σa, a]
    · simp [m, σa, b]
  have hmb : σb ≫ m = b ≫ pullback.diagonal π := by
    apply pullback.hom_ext
    · simp [m, σb]
    · simp [m, σb]
  let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hpre : IsClopen (m ⁻¹' U) := hU.preimage m.continuous
  have hb_mem : σb pt ∈ m ⁻¹' U := by
    change m (σb pt) ∈ U
    rw [← Scheme.Hom.comp_apply, hmb, Scheme.Hom.comp_apply]
    exact hdiag _
  have huniv : m ⁻¹' U = Set.univ := hpre.eq_univ ⟨_, hb_mem⟩
  have ha_mem : σa pt ∈ m ⁻¹' U := by
    rw [huniv]
    exact Set.mem_univ _
  have hpt : m (σa pt) = t := by
    rw [← Scheme.Hom.comp_apply, hma, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply t _
  rw [← hpt]
  exact ha_mem

end Connected

/-! ### Descent along an effective epimorphism -/

section Descent

variable {S S' : Scheme.{u}} (π : S' ⟶ S) {H G : GroupScheme S}
variable (u' : (GroupScheme.baseChange π).obj H ⟶ (GroupScheme.baseChange π).obj G)

/-- The underlying map of `u'` is constant on the fibres of the projection `H_{S'} ⟶ H`, after
composing with the projection `G_{S'} ⟶ G`. -/
def FibreConstant : Prop :=
  ∀ (Z : Scheme.{u}) (x y : Z ⟶ pullback H.X.hom π),
    x ≫ pullback.fst H.X.hom π = y ≫ pullback.fst H.X.hom π →
      x ≫ u'.hom.hom.left ≫ pullback.fst G.X.hom π =
        y ≫ u'.hom.hom.left ≫ pullback.fst G.X.hom π

variable (hc : FibreConstant π u')
variable [EffectiveEpi (pullback.fst H.X.hom π)]

include hc

/-- The underlying scheme map obtained from the effective epimorphism `H_{S'} ⟶ H`. -/
def underlying : H.X.left ⟶ G.X.left :=
  EffectiveEpi.desc (pullback.fst H.X.hom π) (u'.hom.hom.left ≫ pullback.fst G.X.hom π)
    (fun a b hab => hc _ a b hab)

@[reassoc] theorem underlying_fac :
    pullback.fst H.X.hom π ≫ underlying π u' hc =
      u'.hom.hom.left ≫ pullback.fst G.X.hom π :=
  EffectiveEpi.fac _ _ _

/-- The descended map respects the structure morphisms to `S`. -/
theorem underlying_over : underlying π u' hc ≫ G.X.hom = H.X.hom := by
  apply (cancel_epi (pullback.fst H.X.hom π)).mp
  rw [← Category.assoc, underlying_fac]
  have hw : u'.hom.hom.left ≫ pullback.snd G.X.hom π = pullback.snd H.X.hom π :=
    Over.w u'.hom.hom
  simpa only [Category.assoc, pullback.condition] using congrArg (fun q => q ≫ π) hw

/-- The descended morphism in the slice category over `S`. -/
def overHom : H.X ⟶ G.X := Over.homMk (underlying π u' hc) (underlying_over π u' hc)

/-- Pulling the descended morphism back along `π` recovers `u'`. -/
theorem pullback_overHom :
    (Over.pullback π).map (overHom π u' hc) = u'.hom.hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (pullback.lift_fst _ _ _).trans (underlying_fac π u' hc)
  · exact (pullback.lift_snd _ _ _).trans (Over.w u'.hom.hom).symm

variable [(Over.pullback π).Faithful]

/-- The descended morphism is a homomorphism, since the faithful monoidal pullback reflects the
unit and multiplication laws. -/
theorem overHom_isMonHom : IsMonHom (overHom π u' hc) := by
  have : IsMonHom ((Over.pullback π).map (overHom π u' hc)) := by
    rw [pullback_overHom]
    infer_instance
  exact GaloisCocharacterDescent.isMonHom_of_faithfulMap (Over.pullback π) _

/-- The descended homomorphism of group schemes over `S`. -/
def hom : H ⟶ G :=
  letI := overHom_isMonHom π u' hc
  Grp.homMk (overHom π u' hc)

/-- Base change of the descended homomorphism recovers `u'`. -/
theorem baseChange_hom : (GroupScheme.baseChange π).map (hom π u' hc) = u' := by
  apply Grp.hom_ext
  exact pullback_overHom π u' hc

/-- A fibre-constant homomorphism descends uniquely. -/
theorem existsUnique_hom :
    ∃! a : H ⟶ G, (GroupScheme.baseChange π).map a = u' := by
  refine ⟨hom π u' hc, baseChange_hom π u' hc, fun a ha => ?_⟩
  apply Grp.hom_ext
  apply (Over.pullback π).map_injective
  change ((GroupScheme.baseChange π).map a).hom.hom =
    ((GroupScheme.baseChange π).map (hom π u' hc)).hom.hom
  rw [ha, baseChange_hom]

end Descent

/-! ### Rigidity implies descent -/

section Main

variable {S S' : Scheme.{u}} (π : S' ⟶ S) {H G : GroupScheme S}

/-- Separatedness, local finite presentation and quasi-compactness of a group scheme pass to
its base change. -/
theorem baseChange_hom_props {T U : Scheme.{u}} (q : T ⟶ U) (C : GroupScheme U)
    [IsSeparated C.X.hom] [LocallyOfFinitePresentation C.X.hom] [QuasiCompact C.X.hom] :
    IsSeparated ((GroupScheme.baseChange q).obj C).X.hom ∧
      LocallyOfFinitePresentation ((GroupScheme.baseChange q).obj C).X.hom ∧
        QuasiCompact ((GroupScheme.baseChange q).obj C).X.hom :=
  ⟨inferInstanceAs (IsSeparated (pullback.snd C.X.hom q)),
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd C.X.hom q)),
    inferInstanceAs (QuasiCompact (pullback.snd C.X.hom q))⟩

/-- Given rigidity (SGA 3, IX, 5.3), a central `u'` is constant on the fibres of
`H_{S'} ⟶ H` when the geometric fibres of `π` are connected. -/
theorem fibreConstant_of_rigidity (hrig : MultiplicativeTypeCentralRigidityStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    [IsSeparated G.X.hom] [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    (hconn : ∀ (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ S),
      ConnectedSpace ↥(pullback π x))
    (u' : (GroupScheme.baseChange π).obj H ⟶ (GroupScheme.baseChange π).obj G)
    (hu : IsCentral u') : FibreConstant π u' := by
  apply constant_of_eq
  let w := diffHom (u₁ π u') (u₂ π u') (isCentral_u₁ π u' hu) (isCentral_u₂ π u' hu)
  have hA : RelativeMultiplicativeType.IsMultiplicativeType
      ((GroupScheme.baseChange (Descent.fst π)).obj ((GroupScheme.baseChange π).obj H)) :=
    (hH.baseChange π).baseChange (Descent.fst π)
  obtain ⟨h₁, h₂, h₃⟩ := baseChange_hom_props π G
  obtain ⟨h₁', h₂', h₃'⟩ := baseChange_hom_props (Descent.fst π) ((GroupScheme.baseChange π).obj G)
  obtain ⟨-, -, h3⟩ := hrig _ _
    ((GroupScheme.baseChange (Descent.fst π)).obj ((GroupScheme.baseChange π).obj G)) hA
    (Or.inr ⟨h₂', h₃', inferInstance⟩)
  obtain ⟨U, hUc, hUmem, hUtriv⟩ := h3 h₁' w
  have hall : ∀ t, t ∈ U := by
    intro t
    refine mem_of_isClopen_of_diagonal π hconn (U : Set _) ⟨hUc, U.isOpen⟩ ?_ t
    intro y
    rw [SetLike.mem_coe, hUmem, baseChange_diffHom_eq_one_iff, fst_comp_eq_iff]
    let r := Spec.map ((pullback.diagonal π).residueFieldMap y)
    have hr : Flat r ∧ Surjective r := by
      rw [flat_and_surjective_SpecMap_iff]
      let := ((pullback.diagonal π).residueFieldMap y).hom.toAlgebra
      exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
    have := hr.1
    have := hr.2
    apply agree_of_flat_comp _ _ _ _ r
    intro Z α β hαβ
    apply agree_diagonal π u' Z α (β ≫ S'.fromSpecResidueField y)
    rw [hαβ, Category.assoc,
      ← (pullback.diagonal π).SpecMap_residueFieldMap_fromSpecResidueField y]
  have h1 := (baseChange_diffHom_eq_one_iff _ _ _ _ U.ι).mp hUtriv
  rw [fst_comp_eq_iff] at h1
  have hrange : Set.range ((GroupScheme.baseChange (Descent.fst π)).obj
      ((GroupScheme.baseChange π).obj H)).X.hom ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    intro t _
    exact hall t
  have := h1 _ (𝟙 _) (IsOpenImmersion.lift U.ι _ hrange) (by
    rw [IsOpenImmersion.lift_fac, Category.id_comp])
  simpa only [Category.id_comp] using this

/-- **SGA 3, IX, 5.4 from 5.3.** The rigidity of central homomorphisms from groups of
multiplicative type implies their descent along base changes with geometrically connected
fibres. -/
theorem descent_of_rigidity (hrig : MultiplicativeTypeCentralRigidityStatement.{u}) :
    MultiplicativeTypeCentralDescentStatement.{u} := by
  intro S S' π H G hH hGsep hGlfp hGqc hπ hconn u' hu
  have := hGsep
  have := hGlfp
  have := hGqc
  have hc := fibreConstant_of_rigidity π hrig hH hconn u' hu
  rcases hπ with ⟨hfl, hqc, hsu⟩ | ⟨g, hg⟩
  · have := hfl
    have := hqc
    have := hsu
    exact existsUnique_hom π u' hc
  · have : ∀ (Z : Scheme.{u}) (f : Z ⟶ S), IsSplitEpi (pullback.fst f π) := fun Z f =>
      IsSplitEpi.mk' ⟨pullback.lift (𝟙 _) (f ≫ g) (by simp [hg]), by simp⟩
    exact existsUnique_hom π u' hc

end Main

end Langlands.GroupScheme.MultiplicativeTypeCentralDescent
