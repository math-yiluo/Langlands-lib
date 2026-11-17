import Langlands.GroupScheme.Torus.DiagonalizableAtlasComparison
import Langlands.GroupScheme.Descent.DisjointGroupGluing

/-! # The glued free-cover group of a diagonalizable atlas and its descent datum -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeMultiplicativeType

open Descent CoproductComponents FreeCharacterCover

/-! ### Conjugating isomorphisms of diagonalizable groups into base changes -/

section Conj

variable {X V W : Scheme.{u}} {Λ Λ' Λ'' : Type u} [AddCommGroup Λ] [AddCommGroup Λ']
  [AddCommGroup Λ'']

/-- An isomorphism `D_V(Λ) ≅ D_V(Λ')`, written between base changes of `D_X(Λ)` and
`D_X(Λ')` along two maps `a b : V ⟶ X`. -/
def dconj (a b : V ⟶ X) (u : diagonalizable V Λ ≅ diagonalizable V Λ') :
    (GroupScheme.baseChange a).obj (diagonalizable X Λ) ≅
      (GroupScheme.baseChange b).obj (diagonalizable X Λ') :=
  diagonalizableBaseChangeIso a Λ ≪≫ u ≪≫ (diagonalizableBaseChangeIso b Λ').symm

theorem pullIso_dconj (a b : V ⟶ X) (u : diagonalizable V Λ ≅ diagonalizable V Λ')
    (q : W ⟶ V) {a' b' : W ⟶ X} (hqa : q ≫ a = a') (hqb : q ≫ b = b') :
    pullIso q hqa hqb (dconj a b u) = dconj a' b' (dpullIso q u) := by
  apply Iso.ext
  have h := dpull_conj q hqa hqb ((diagonalizableBaseChangeIso a Λ).hom ≫ u.hom ≫
    (diagonalizableBaseChangeIso b Λ').inv)
  simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  simp only [dconj, pullIso_hom, Iso.trans_hom, Iso.symm_hom, dpullIso_hom, h,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

@[simp] theorem dconj_refl (a : V ⟶ X) :
    dconj a a (Iso.refl (diagonalizable V Λ)) = Iso.refl _ := by
  ext
  simp [dconj]

theorem dconj_trans (a b c : V ⟶ X) (u : diagonalizable V Λ ≅ diagonalizable V Λ')
    (v : diagonalizable V Λ' ≅ diagonalizable V Λ'') :
    dconj a b u ≪≫ dconj b c v = dconj a c (u ≪≫ v) := by
  ext
  simp [dconj]

end Conj

/-- Direct pullback of the inverse of an isomorphism. -/
theorem pullIso_symm {S T U : Scheme.{u}} (q : U ⟶ T) {f g : T ⟶ S} {r s : U ⟶ S}
    (hf : q ≫ f = r) (hg : q ≫ g = s) {G H : GroupScheme S}
    (e : (GroupScheme.baseChange f).obj G ≅ (GroupScheme.baseChange g).obj H) :
    pullIso q hg hf e.symm = (pullIso q hf hg e).symm :=
  rfl

namespace DiagonalizableAtlas

variable {S T V W : Scheme.{u}} {H : GroupScheme S} (A : DiagonalizableAtlas H)

/-! ### The atlas scheme and the glued group -/

/-- The disjoint union of the charts. -/
abbrev space : Scheme.{u} := ∐ A.Z

/-- The inclusion of a chart into the atlas scheme. -/
abbrev inclusion (i : A.I) : A.Z i ⟶ A.space := Sigma.ι A.Z i

/-- The projection of the atlas scheme to the base. -/
abbrev projection : A.space ⟶ S := Sigma.desc A.f

@[reassoc (attr := simp)] theorem inclusion_projection (i : A.I) :
    A.inclusion i ≫ A.projection = A.f i :=
  Sigma.ι_comp_desc _ _

instance inclusion_isIso : IsIso (Sigma.desc A.inclusion) := by
  simpa only [Sigma.desc_ι] using (inferInstance : IsIso (𝟙 A.space))

/-- The model group `D(F(Λ i))` on the `i`-th chart. -/
abbrev model (i : A.I) : GroupScheme (A.Z i) := diagonalizable (A.Z i) (Cover (A.Λ i))

/-- The group over the atlas scheme which is `D(F(Λ i))` on the `i`-th chart. -/
def group : GroupScheme A.space := DisjointGroupGluing.group A.inclusion A.model

/-- The glued group on a chart, written as a base change of a group over the atlas scheme. -/
def groupChart (i : A.I) :
    (GroupScheme.baseChange (A.inclusion i)).obj A.group ≅
      (GroupScheme.baseChange (A.inclusion i)).obj (diagonalizable A.space (Cover (A.Λ i))) :=
  DisjointGroupGluing.componentIso A.inclusion A.model i ≪≫
    (diagonalizableBaseChangeIso (A.inclusion i) (Cover (A.Λ i))).symm

/-- The description of `a^* G` given by a chart coordinate `x` of `a : V ⟶ space`. -/
def coord (i : A.I) (x : V ⟶ A.Z i) (a : V ⟶ A.space) (hx : x ≫ A.inclusion i = a) :
    (GroupScheme.baseChange a).obj A.group ≅
      (GroupScheme.baseChange a).obj (diagonalizable A.space (Cover (A.Λ i))) :=
  pullIso x hx hx (A.groupChart i)

/-! ### Transitions on chart coordinates -/

/-- The transition between two points of the atlas scheme over the same point of the base,
given chart coordinates of both points. -/
def chartValue (i j : A.I) (x : V ⟶ A.Z i) (y : V ⟶ A.Z j) (a b : V ⟶ A.space)
    (hx : x ≫ A.inclusion i = a) (hy : y ≫ A.inclusion j = b) (l : V ⟶ S)
    (hxl : x ≫ A.f i = l) (hyl : y ≫ A.f j = l) :
    (GroupScheme.baseChange a).obj A.group ≅ (GroupScheme.baseChange b).obj A.group :=
  A.coord i x a hx ≪≫ dconj a b (A.lift i j x y l hxl hyl) ≪≫ (A.coord j y b hy).symm

theorem chartValue_pull (i j : A.I) (x : V ⟶ A.Z i) (y : V ⟶ A.Z j) (a b : V ⟶ A.space)
    (hx : x ≫ A.inclusion i = a) (hy : y ≫ A.inclusion j = b) (l : V ⟶ S)
    (hxl : x ≫ A.f i = l) (hyl : y ≫ A.f j = l)
    (q : W ⟶ V) {a' b' : W ⟶ A.space} (hqa : q ≫ a = a') (hqb : q ≫ b = b')
    {l' : W ⟶ S} (hql : q ≫ l = l') :
    pullIso q hqa hqb (A.chartValue i j x y a b hx hy l hxl hyl) =
      A.chartValue i j (q ≫ x) (q ≫ y) a' b' (by rw [Category.assoc, hx, hqa])
        (by rw [Category.assoc, hy, hqb]) l' (by rw [Category.assoc, hxl, hql])
        (by rw [Category.assoc, hyl, hql]) := by
  subst hqa hqb hql
  unfold chartValue coord
  rw [pullIso_trans q rfl rfl rfl, pullIso_trans q rfl rfl rfl, pullIso_symm,
    pullIso_pullIso, pullIso_pullIso, pullIso_dconj, dpullIso_lift]

@[simp] theorem chartValue_self (i : A.I) (x : V ⟶ A.Z i) (a : V ⟶ A.space)
    (hx : x ≫ A.inclusion i = a) (l : V ⟶ S) (hxl : x ≫ A.f i = l) :
    A.chartValue i i x x a a hx hx l hxl hxl = Iso.refl _ := by
  simp [chartValue]

theorem chartValue_trans (i j k : A.I) (x : V ⟶ A.Z i) (y : V ⟶ A.Z j) (z : V ⟶ A.Z k)
    (a b c : V ⟶ A.space) (hx : x ≫ A.inclusion i = a) (hy : y ≫ A.inclusion j = b)
    (hz : z ≫ A.inclusion k = c) (l : V ⟶ S)
    (hxl : x ≫ A.f i = l) (hyl : y ≫ A.f j = l) (hzl : z ≫ A.f k = l) :
    A.chartValue i j x y a b hx hy l hxl hyl ≪≫ A.chartValue j k y z b c hy hz l hyl hzl =
      A.chartValue i k x z a c hx hz l hxl hzl := by
  unfold chartValue
  rw [← A.lift_trans i j k x y z l hxl hyl hzl, ← dconj_trans a b c]
  ext
  simp

/-! ### Assembled transitions -/

/-- Recover the chart's base map from an actual coordinate factorization. -/
theorem coordinate_base (a : T ⟶ A.space) (k : T ⟶ S)
    (ha : a ≫ A.projection = k) (i : A.I) (q : W ⟶ T)
    (x : W ⟶ A.Z i) (hx : x ≫ A.inclusion i = q ≫ a) (l : W ⟶ S) (hl : q ≫ k = l) :
    x ≫ A.f i = l := by
  rw [← A.inclusion_projection i, ← Category.assoc, hx, Category.assoc, ha, hl]

/-- Assemble the transition from a chart coordinate to an arbitrary atlas-valued map. -/
def chartToAtlas (i : A.I) (x : T ⟶ A.Z i) (a b : T ⟶ A.space) (k : T ⟶ S)
    (hx : x ≫ A.inclusion i = a) (hxk : x ≫ A.f i = k) (hb : b ≫ A.projection = k) :
    (GroupScheme.baseChange a).obj A.group ≅ (GroupScheme.baseChange b).obj A.group :=
  DisjointComponents.pullbackIsoAlong (toBase b) (fun _ => rfl) (fun _ => rfl)
    (fun j => A.chartValue i j (toBase b j ≫ x) (toComponent b j) (toBase b j ≫ a)
      (toBase b j ≫ b) (by rw [Category.assoc, hx]) (component_condition b j)
      (toBase b j ≫ k) (by rw [Category.assoc, hxk])
      (A.coordinate_base b k hb j (toBase b j) (toComponent b j)
        (component_condition b j) _ rfl))

/-- Evaluate a chart-to-atlas transition on any chart coordinate of the target. -/
theorem chartToAtlas_on_chart (i : A.I) (x : T ⟶ A.Z i) (a b : T ⟶ A.space) (k : T ⟶ S)
    (hx : x ≫ A.inclusion i = a) (hxk : x ≫ A.f i = k) (hb : b ≫ A.projection = k)
    (j : A.I) (q : W ⟶ T) (y : W ⟶ A.Z j) (hy : y ≫ A.inclusion j = q ≫ b)
    {a' b' : W ⟶ A.space} (hqa : q ≫ a = a') (hqb : q ≫ b = b')
    (l : W ⟶ S) (hl : q ≫ k = l) :
    pullIso q hqa hqb (A.chartToAtlas i x a b k hx hxk hb) =
      A.chartValue i j (q ≫ x) y a' b' (by rw [Category.assoc, hx, hqa])
        (hy.trans hqb) l (by rw [Category.assoc, hxk, hl])
        (A.coordinate_base b k hb j q y hy l hl) := by
  let v := CoproductComponents.lift b j q y hy
  have hv : v ≫ toBase b j = q := lift_toBase b j q y hy
  unfold chartToAtlas
  rw [DisjointComponents.pullIso_pullbackIsoAlong_factor
    (toBase b) (fun _ => rfl) (fun _ => rfl) _ j v hv hqa hqb]
  rw [A.chartValue_pull _ _ _ _ _ _ _ _ _ _ _ v _ _ (by rw [← Category.assoc, hv, hl])]
  simp only [v, lift_toBase_assoc, lift_toComponent]

/-- Assemble transitions between two arbitrary atlas-valued maps over the base. -/
def transition (a b : T ⟶ A.space) (k : T ⟶ S)
    (ha : a ≫ A.projection = k) (hb : b ≫ A.projection = k) :
    (GroupScheme.baseChange a).obj A.group ≅ (GroupScheme.baseChange b).obj A.group :=
  DisjointComponents.pullbackIsoAlong (toBase a) (fun _ => rfl) (fun _ => rfl)
    (fun i => A.chartToAtlas i (toComponent a i) (toBase a i ≫ a) (toBase a i ≫ b)
      (toBase a i ≫ k) (component_condition a i)
      (A.coordinate_base a k ha i (toBase a i) (toComponent a i)
        (component_condition a i) _ rfl)
      (by rw [Category.assoc, hb]))

/-- The assembled transition has the prescribed value on every pair of chart coordinates. -/
theorem transition_on_charts (a b : T ⟶ A.space) (k : T ⟶ S)
    (ha : a ≫ A.projection = k) (hb : b ≫ A.projection = k)
    (i j : A.I) (q : W ⟶ T) (x : W ⟶ A.Z i) (y : W ⟶ A.Z j)
    {a' b' : W ⟶ A.space} (hqa : q ≫ a = a') (hqb : q ≫ b = b')
    (hx : x ≫ A.inclusion i = a') (hy : y ≫ A.inclusion j = b')
    (l : W ⟶ S) (hl : q ≫ k = l) :
    pullIso q hqa hqb (A.transition a b k ha hb) =
      A.chartValue i j x y a' b' hx hy l
        (A.coordinate_base a k ha i q x (hx.trans hqa.symm) l hl)
        (A.coordinate_base b k hb j q y (hy.trans hqb.symm) l hl) := by
  let v := CoproductComponents.lift a i q x (hx.trans hqa.symm)
  have hv : v ≫ toBase a i = q := lift_toBase a i q x _
  have hvy : y ≫ A.inclusion j = v ≫ (toBase a i ≫ b) := by
    rw [← Category.assoc, hv, hy, hqb]
  unfold transition
  rw [DisjointComponents.pullIso_pullbackIsoAlong_factor
    (toBase a) (fun _ => rfl) (fun _ => rfl) _ i v hv hqa hqb]
  rw [A.chartToAtlas_on_chart _ _ _ _ _ _ _ _ j v y hvy
    (by rw [← Category.assoc, hv, hqa]) (by rw [← Category.assoc, hv, hqb]) l
    (by rw [← Category.assoc, hv, hl])]
  simp only [v, lift_toComponent]

/-- Two isomorphisms agree if they agree on all pairs of chart coordinates. -/
theorem iso_ext_on_charts (a b : T ⟶ A.space)
    {e d : (GroupScheme.baseChange a).obj A.group ≅ (GroupScheme.baseChange b).obj A.group}
    (h : ∀ (V : Scheme.{u}) (i j : A.I) (q : V ⟶ T) (x : V ⟶ A.Z i) (y : V ⟶ A.Z j),
      x ≫ A.inclusion i = q ≫ a → y ≫ A.inclusion j = q ≫ b →
      pullIso q rfl rfl e = pullIso q rfl rfl d) : e = d := by
  apply DisjointComponents.pullIso_ext_along (toBase a) (fun _ => rfl) (fun _ => rfl)
  intro i
  apply DisjointComponents.pullIso_ext_along
    (toBase (toBase a i ≫ b)) (fun _ => rfl) (fun _ => rfl)
  intro j
  rw [pullIso_pullIso, pullIso_pullIso]
  apply h _ i j _ (toBase (toBase a i ≫ b) j ≫ toComponent a i)
    (toComponent (toBase a i ≫ b) j)
  · simp only [Category.assoc, component_condition]
  · simpa only [Category.assoc] using component_condition (toBase a i ≫ b) j

/-- Two homomorphisms agree if they agree on all pairs of chart coordinates. -/
theorem hom_ext_on_charts (a b : T ⟶ A.space) {G' H' : GroupScheme A.space}
    {e d : (GroupScheme.baseChange a).obj G' ⟶ (GroupScheme.baseChange b).obj H'}
    (h : ∀ (V : Scheme.{u}) (i j : A.I) (q : V ⟶ T) (x : V ⟶ A.Z i) (y : V ⟶ A.Z j),
      x ≫ A.inclusion i = q ≫ a → y ≫ A.inclusion j = q ≫ b →
      pullHom q rfl rfl e = pullHom q rfl rfl d) : e = d := by
  apply DisjointComponents.pullHom_ext_along (toBase a) (fun _ => rfl) (fun _ => rfl)
  intro i
  apply DisjointComponents.pullHom_ext_along
    (toBase (toBase a i ≫ b)) (fun _ => rfl) (fun _ => rfl)
  intro j
  rw [pullHom_pullHom, pullHom_pullHom]
  apply h _ i j _ (toBase (toBase a i ≫ b) j ≫ toComponent a i)
    (toComponent (toBase a i ≫ b) j)
  · simp only [Category.assoc, component_condition]
  · simpa only [Category.assoc] using component_condition (toBase a i ≫ b) j

/-- Triple chart coordinates detect equality of isomorphisms. -/
theorem iso_ext_on_three_charts (a b c : T ⟶ A.space)
    {e d : (GroupScheme.baseChange a).obj A.group ≅ (GroupScheme.baseChange c).obj A.group}
    (h : ∀ (V : Scheme.{u}) (i j n : A.I) (q : V ⟶ T)
      (x : V ⟶ A.Z i) (y : V ⟶ A.Z j) (z : V ⟶ A.Z n),
      x ≫ A.inclusion i = q ≫ a → y ≫ A.inclusion j = q ≫ b →
      z ≫ A.inclusion n = q ≫ c →
      pullIso q rfl rfl e = pullIso q rfl rfl d) : e = d := by
  apply A.iso_ext_on_charts a c
  intro V i n q x z hx hz
  apply DisjointComponents.pullIso_ext_along
    (toBase (q ≫ b)) (fun _ => rfl) (fun _ => rfl)
  intro j
  rw [pullIso_pullIso, pullIso_pullIso]
  apply h _ i j n _ (toBase (q ≫ b) j ≫ x) (toComponent (q ≫ b) j)
    (toBase (q ≫ b) j ≫ z)
  · simp only [Category.assoc, hx]
  · simpa only [Category.assoc] using component_condition (q ≫ b) j
  · simp only [Category.assoc, hz]

@[simp] theorem transition_self (a : T ⟶ A.space) (k : T ⟶ S) (ha : a ≫ A.projection = k) :
    A.transition a a k ha ha = Iso.refl _ := by
  apply DisjointComponents.pullIso_ext_along (toBase a) (fun _ => rfl) (fun _ => rfl)
  intro i
  rw [A.transition_on_charts a a k ha ha i i (toBase a i)
    (toComponent a i) (toComponent a i) rfl rfl (component_condition a i)
    (component_condition a i) _ rfl, chartValue_self]
  simp [pullIso]

/-- The assembled transition commutes with every further pullback. -/
theorem transition_pull (a b : T ⟶ A.space) (k : T ⟶ S)
    (ha : a ≫ A.projection = k) (hb : b ≫ A.projection = k)
    (q : W ⟶ T) {a' b' : W ⟶ A.space} (hqa : q ≫ a = a') (hqb : q ≫ b = b')
    (l : W ⟶ S) (hl : q ≫ k = l) :
    pullIso q hqa hqb (A.transition a b k ha hb) =
      A.transition a' b' l (by rw [← hqa, Category.assoc, ha, hl])
        (by rw [← hqb, Category.assoc, hb, hl]) := by
  apply A.iso_ext_on_charts a' b'
  intro V i j r x y hx hy
  rw [pullIso_pullIso]
  rw [A.transition_on_charts a b k ha hb i j (r ≫ q) x y
    (by rw [Category.assoc, hqa]) (by rw [Category.assoc, hqb]) hx hy _
    (by rw [Category.assoc, hl])]
  rw [A.transition_on_charts a' b' l _ _ i j r x y rfl rfl hx hy _ rfl]

/-- The assembled transitions satisfy the cocycle condition. -/
theorem transition_trans (a b c : T ⟶ A.space) (k : T ⟶ S)
    (ha : a ≫ A.projection = k) (hb : b ≫ A.projection = k)
    (hc : c ≫ A.projection = k) :
    A.transition a c k ha hc = A.transition a b k ha hb ≪≫ A.transition b c k hb hc := by
  apply A.iso_ext_on_three_charts a b c
  intro V i j n q x y z hx hy hz
  rw [pullIso_trans q rfl rfl rfl]
  rw [A.transition_on_charts a c k ha hc i n q x z rfl rfl hx hz _ rfl,
    A.transition_on_charts a b k ha hb i j q x y rfl rfl hx hy _ rfl,
    A.transition_on_charts b c k hb hc j n q y z rfl rfl hy hz _ rfl]
  exact (A.chartValue_trans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).symm

/-! ### The descent datum -/

/-- The overlap isomorphism of the glued group. -/
def overlap : OverlapIso A.projection A.group :=
  A.transition (fst A.projection) (snd A.projection)
    (fst A.projection ≫ A.projection) rfl pullback.condition.symm

private theorem triple_base2 (p : A.space ⟶ S) :
    p23 p ≫ fst p ≫ p = p1 p ≫ p := by
  rw [← Category.assoc, p23_fst]
  dsimp only [p1, p2]
  rw [Category.assoc, Category.assoc, pullback.condition]

private theorem triple_base3 (p : A.space ⟶ S) :
    p13 p ≫ fst p ≫ p = p1 p ≫ p := by
  rw [← Category.assoc, p13_fst]

/-- The overlap satisfies the cocycle condition. -/
theorem overlap_cocycle : Descent.Cocycle A.overlap := by
  change (pullIso (p12 A.projection) rfl rfl A.overlap).hom ≫
      (pullIso (p23 A.projection) (p23_fst A.projection) rfl A.overlap).hom =
    (pullIso (p13 A.projection) (p13_fst A.projection) (p13_snd A.projection) A.overlap).hom
  unfold overlap
  rw [A.transition_pull _ _ _ _ _ (p12 A.projection) rfl rfl _ (Category.assoc _ _ _).symm,
    A.transition_pull _ _ _ _ _ (p23 A.projection) (p23_fst A.projection) rfl _
      (triple_base2 A A.projection),
    A.transition_pull _ _ _ _ _ (p13 A.projection) (p13_fst A.projection)
      (p13_snd A.projection) _ (triple_base3 A A.projection)]
  exact (congrArg Iso.hom (A.transition_trans _ _ _ _ _ _ _)).symm

/-- The descent datum of the glued group along the atlas projection. -/
def datum : Datum A.projection A.group where
  overlap := A.overlap
  cocycle := A.overlap_cocycle

/-- Every pullback of the overlap has the prescribed chart values. -/
theorem overlap_on_charts (q : V ⟶ Overlap A.projection) (i j : A.I)
    (x : V ⟶ A.Z i) (y : V ⟶ A.Z j) {a b : V ⟶ A.space}
    (ha : q ≫ fst A.projection = a) (hb : q ≫ snd A.projection = b)
    (hx : x ≫ A.inclusion i = a) (hy : y ≫ A.inclusion j = b) (l : V ⟶ S)
    (hxl : x ≫ A.f i = l) (hyl : y ≫ A.f j = l) :
    pullIso q ha hb A.overlap = A.chartValue i j x y a b hx hy l hxl hyl := by
  unfold overlap
  rw [A.transition_on_charts _ _ _ _ _ i j q x y ha hb hx hy l
    (by rw [← Category.assoc, ha, ← hx, Category.assoc, inclusion_projection, hxl])]

end DiagonalizableAtlas

end Langlands.GroupScheme.RelativeMultiplicativeType
