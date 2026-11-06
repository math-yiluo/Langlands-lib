import Langlands.GroupScheme.Rational.FiniteGaloisTwistExistenceStatement
import Langlands.GroupScheme.Descent.AffineEffectivityProof
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.Multiplicative

/-! # Existence of finite-Galois twisted forms -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace PointDescent

variable {B S : Scheme.{u}} (p : S ⟶ B)

/-- Precomposition with an isomorphism of test objects, on group points. -/
def pointsCongr {Z Y : Over B} (j : Z ≅ Y) (X : GroupScheme B) :
    (Y ⟶ X.X) ≃* (Z ⟶ X.X) where
  toFun y := j.hom ≫ y
  invFun z := j.inv ≫ z
  left_inv y := by simp
  right_inv z := by simp
  map_mul' y y' := MonObj.comp_mul _ _ _

/-- Postcomposition with an isomorphism of group schemes, on group points. -/
def pointsIso {S' : Scheme.{u}} {X Y : GroupScheme S'} (e : X ≅ Y) (T : Over S') :
    (T ⟶ X.X) ≃* (T ⟶ Y.X) where
  toFun x := x ≫ e.hom.hom.hom
  invFun y := y ≫ e.inv.hom.hom
  left_inv x := by
    change x ≫ e.hom.hom.hom ≫ e.inv.hom.hom = x
    rw [← Grp.comp_hom_hom, e.hom_inv_id]
    simp
  right_inv y := by
    change y ≫ e.inv.hom.hom ≫ e.hom.hom.hom = y
    rw [← Grp.comp_hom_hom, e.inv_hom_id]
    simp
  map_mul' x x' := MonObj.mul_comp _ _ _

theorem comp_hom_comp_inv {S' : Scheme.{u}} {X Y : GroupScheme S'} (e : X ≅ Y) {T : Over S'}
    (x : T ⟶ X.X) : (x ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = x :=
  (pointsIso e T).left_inv x

theorem comp_inv_comp_hom {S' : Scheme.{u}} {X Y : GroupScheme S'} (e : X ≅ Y) {T : Over S'}
    (y : T ⟶ Y.X) : (y ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = y :=
  (pointsIso e T).right_inv y

/-- Points of the base change along `p` over `V`, read as points of the original group
over the object of `Over B` with the same underlying scheme and structure map `k`. -/
def baseChangePoints (X : GroupScheme B) (V : Over S) (k : V.left ⟶ B)
    (h : V.hom ≫ p = k) :
    (V ⟶ ((baseChange p).obj X).X) ≃* (Over.mk k ⟶ X.X) :=
  (baseChangePointsEquiv p X V).trans
    (pointsCongr (Z := Over.mk k) (Y := (Over.map p).obj V)
      (Over.isoMk (Iso.refl V.left) (by simpa using h)) X)

@[simp] theorem baseChangePoints_left (X : GroupScheme B) (V : Over S) (k : V.left ⟶ B)
    (h : V.hom ≫ p = k) (x : V ⟶ ((baseChange p).obj X).X) :
    (baseChangePoints p X V k h x).left = x.left ≫ pullback.fst X.X.hom p := by
  change 𝟙 V.left ≫ x.left ≫ pullback.fst X.X.hom p = _
  exact Category.id_comp _

theorem baseChangePoints_naturality (X : GroupScheme B) {V V' : Over S} (t : V' ⟶ V)
    (k : V.left ⟶ B) (h : V.hom ≫ p = k) (k' : V'.left ⟶ B) (h' : V'.hom ≫ p = k')
    (τ : Over.mk k' ⟶ Over.mk k) (hτ : τ.left = t.left) (y : V ⟶ ((baseChange p).obj X).X) :
    baseChangePoints p X V' k' h' (t ≫ y) = τ ≫ baseChangePoints p X V k h y := by
  apply Over.OverMorphism.ext
  simp only [baseChangePoints_left, Over.comp_left, hτ, Category.assoc]

theorem baseChangePoints_symm_naturality (X : GroupScheme B) {V V' : Over S} (t : V' ⟶ V)
    (k : V.left ⟶ B) (h : V.hom ≫ p = k) (k' : V'.left ⟶ B) (h' : V'.hom ≫ p = k')
    (τ : Over.mk k' ⟶ Over.mk k) (hτ : τ.left = t.left) (z : Over.mk k ⟶ X.X) :
    (baseChangePoints p X V' k' h').symm (τ ≫ z) = t ≫ (baseChangePoints p X V k h).symm z := by
  apply (baseChangePoints p X V' k' h').injective
  rw [MulEquiv.apply_symm_apply, baseChangePoints_naturality p X t k h k' h' τ hτ,
    MulEquiv.apply_symm_apply]

variable (G : GroupScheme B)

/-- Points of an iterated base change `r^*(p^*G)` over `W`, read as points of `G`. -/
def iteratedPoints {T : Scheme.{u}} (r : T ⟶ S) (W : Over T) (k : W.left ⟶ B)
    (h : W.hom ≫ r ≫ p = k) :
    (W ⟶ ((baseChange r).obj ((baseChange p).obj G)).X) ≃* (Over.mk k ⟶ G.X) :=
  (baseChangePointsEquiv r ((baseChange p).obj G) W).trans
    (baseChangePoints p G ((Over.map r).obj W) k (by simpa using h))

@[simp] theorem iteratedPoints_left {T : Scheme.{u}} (r : T ⟶ S) (W : Over T)
    (k : W.left ⟶ B) (h : W.hom ≫ r ≫ p = k)
    (x : W ⟶ ((baseChange r).obj ((baseChange p).obj G)).X) :
    (iteratedPoints p G r W k h x).left =
      x.left ≫ pullback.fst ((baseChange p).obj G).X.hom r ≫ pullback.fst G.X.hom p := by
  change 𝟙 W.left ≫ (x.left ≫ pullback.fst ((baseChange p).obj G).X.hom r) ≫
    pullback.fst G.X.hom p = _
  rw [Category.id_comp, Category.assoc]

theorem iteratedPoints_naturality {T : Scheme.{u}} (r : T ⟶ S) {W W' : Over T}
    (t : W' ⟶ W) (k : W.left ⟶ B) (h : W.hom ≫ r ≫ p = k) (k' : W'.left ⟶ B)
    (h' : W'.hom ≫ r ≫ p = k') (ht : t.left ≫ k = k')
    (x : W ⟶ ((baseChange r).obj ((baseChange p).obj G)).X) :
    iteratedPoints p G r W' k' h' (t ≫ x) =
      (Over.homMk t.left ht : Over.mk k' ⟶ Over.mk k) ≫ iteratedPoints p G r W k h x := by
  apply Over.OverMorphism.ext
  simp only [iteratedPoints_left, Over.comp_left, Over.homMk_left, Category.assoc]

/-- An iterated base change along a composite, compared with the direct base change. -/
theorem iteratedPoints_comparison {T U : Scheme.{u}} (f : T ⟶ S) (q : U ⟶ T) (r : U ⟶ S)
    (hq : q ≫ f = r) (Z : Over U) (k : Z.left ⟶ B) (h : Z.hom ≫ r ≫ p = k)
    (h' : ((Over.map q).obj Z).hom ≫ f ≫ p = k)
    (w : Z ⟶ ((baseChange q).obj ((baseChange f).obj ((baseChange p).obj G))).X) :
    iteratedPoints p G r Z k h
        (w ≫ (Descent.pullbackComparison f q r hq ((baseChange p).obj G)).hom.hom.hom) =
      iteratedPoints p G f ((Over.map q).obj Z) k h'
        (baseChangePointsEquiv q ((baseChange f).obj ((baseChange p).obj G)) Z w) := by
  apply Over.OverMorphism.ext
  simp only [iteratedPoints_left, Over.comp_left, Category.assoc,
    Descent.pullbackComparison_hom_fst_assoc]
  rfl

/-- Points of an iterated base change followed by a base-changed homomorphism. -/
theorem iteratedPoints_map {Y : GroupScheme B} {T : Scheme.{u}} (r : T ⟶ S) (W : Over T)
    (k : W.left ⟶ B) (h : W.hom ≫ r ≫ p = k)
    (f : (baseChange p).obj Y ⟶ (baseChange p).obj G)
    (u : W ⟶ ((baseChange r).obj ((baseChange p).obj Y)).X) :
    iteratedPoints p G r W k h (u ≫ ((baseChange r).map f).hom.hom) =
      baseChangePoints p G ((Over.map r).obj W) k (by simpa using h)
        (baseChangePointsEquiv r ((baseChange p).obj Y) W u ≫ f.hom.hom) := by
  change baseChangePoints p G ((Over.map r).obj W) k (by simpa using h)
      (baseChangePointsEquiv r ((baseChange p).obj G) W
        (u ≫ ((baseChange r).map f).hom.hom)) = _
  rw [baseChangePointsEquiv_comp]

/-- The canonical overlap identification does not move points of the original group. -/
theorem iteratedPoints_canonicalOverlap (W : Over (Descent.Overlap p)) (k : W.left ⟶ B)
    (h₁ : W.hom ≫ Descent.fst p ≫ p = k) (h₂ : W.hom ≫ Descent.snd p ≫ p = k)
    (u : W ⟶ ((baseChange (Descent.fst p)).obj ((baseChange p).obj G)).X) :
    iteratedPoints p G (Descent.snd p) W k h₂
        (u ≫ (Descent.canonicalOverlap p G).hom.hom.hom) =
      iteratedPoints p G (Descent.fst p) W k h₁ u := by
  apply Over.OverMorphism.ext
  simp only [iteratedPoints_left, Over.comp_left, Category.assoc,
    Descent.canonicalOverlap_fst]

/-- The cover `S → B` as an object over `B`. -/
abbrev cover : Over B := Over.mk p

/-- A natural cocycle of point automorphisms of `G` on the pairs of points of the cover:
the point-level form of a descent datum on `p^*G`. -/
structure PointOverlap where
  /-- The automorphism carrying the coordinate `b` to the coordinate `c`. -/
  toFun : ∀ {Z : Over B} (_ _ : Z ⟶ cover p), (Z ⟶ G.X) ≃* (Z ⟶ G.X)
  naturality : ∀ {Z Z' : Over B} (t : Z' ⟶ Z) (b c : Z ⟶ cover p) (g : Z ⟶ G.X),
    toFun (t ≫ b) (t ≫ c) (t ≫ g) = t ≫ toFun b c g
  cocycle : ∀ {Z : Over B} (b c d : Z ⟶ cover p) (g : Z ⟶ G.X),
    toFun c d (toFun b c g) = toFun b d g

variable {p G} (φ : PointOverlap p G)

/-- The first coordinate of a point of the double overlap, as a point of the cover. -/
def firstPoint {Y : Scheme.{u}} (m : Y ⟶ Descent.Overlap p) (k : Y ⟶ B)
    (h : m ≫ Descent.fst p ≫ p = k) : Over.mk k ⟶ cover p :=
  Over.homMk (m ≫ Descent.fst p) (by simpa using h)

/-- The second coordinate of a point of the double overlap, as a point of the cover. -/
def secondPoint {Y : Scheme.{u}} (m : Y ⟶ Descent.Overlap p) (k : Y ⟶ B)
    (h : m ≫ Descent.snd p ≫ p = k) : Over.mk k ⟶ cover p :=
  Over.homMk (m ≫ Descent.snd p) (by simpa using h)

theorem overlap_condition {Y : Scheme.{u}} (m : Y ⟶ Descent.Overlap p) :
    m ≫ Descent.snd p ≫ p = m ≫ Descent.fst p ≫ p := by
  rw [pullback.condition]

/-- The overlap transport on points over a test `W` of the double overlap. -/
def overlapPoints (W : Over (Descent.Overlap p)) :
    (W ⟶ ((baseChange (Descent.fst p)).obj ((baseChange p).obj G)).X) ≃*
      (W ⟶ ((baseChange (Descent.snd p)).obj ((baseChange p).obj G)).X) :=
  (iteratedPoints p G (Descent.fst p) W _ rfl).trans
    ((φ.toFun (firstPoint W.hom _ rfl) (secondPoint W.hom _ (overlap_condition W.hom))).trans
      (iteratedPoints p G (Descent.snd p) W _ (overlap_condition W.hom)).symm)

theorem iteratedPoints_overlapPoints (W : Over (Descent.Overlap p))
    (x : W ⟶ ((baseChange (Descent.fst p)).obj ((baseChange p).obj G)).X)
    (k : W.left ⟶ B) (h₁ : W.hom ≫ Descent.fst p ≫ p = k)
    (h₂ : W.hom ≫ Descent.snd p ≫ p = k) :
    iteratedPoints p G (Descent.snd p) W k h₂ (overlapPoints φ W x) =
      φ.toFun (firstPoint W.hom k h₁) (secondPoint W.hom k h₂)
        (iteratedPoints p G (Descent.fst p) W k h₁ x) := by
  subst h₁
  exact MulEquiv.apply_symm_apply _ _

theorem overlapPoints_naturality {W W' : Over (Descent.Overlap p)} (t : W' ⟶ W)
    (x : W ⟶ ((baseChange (Descent.fst p)).obj ((baseChange p).obj G)).X) :
    overlapPoints φ W' (t ≫ x) = t ≫ overlapPoints φ W x := by
  have hk : t.left ≫ W.hom ≫ Descent.fst p ≫ p = W'.hom ≫ Descent.fst p ≫ p := by
    rw [← Over.w t, Category.assoc]
  let τ : Over.mk (W'.hom ≫ Descent.fst p ≫ p) ⟶ Over.mk (W.hom ≫ Descent.fst p ≫ p) :=
    Over.homMk t.left hk
  apply (iteratedPoints p G (Descent.snd p) W' _ (overlap_condition W'.hom)).injective
  rw [iteratedPoints_overlapPoints φ W' (t ≫ x) _ rfl,
    iteratedPoints_naturality p G (Descent.fst p) t _ rfl _ rfl hk,
    iteratedPoints_naturality p G (Descent.snd p) t _ (overlap_condition W.hom) _
      (overlap_condition W'.hom) hk,
    iteratedPoints_overlapPoints φ W x _ rfl]
  have hb : firstPoint W'.hom _ rfl = τ ≫ firstPoint W.hom _ rfl := by
    apply Over.OverMorphism.ext
    change W'.hom ≫ Descent.fst p = t.left ≫ W.hom ≫ Descent.fst p
    rw [← Category.assoc, Over.w t]
  have hc : secondPoint W'.hom _ (overlap_condition W'.hom) =
      τ ≫ secondPoint W.hom _ (overlap_condition W.hom) := by
    apply Over.OverMorphism.ext
    change W'.hom ≫ Descent.snd p = t.left ≫ W.hom ≫ Descent.snd p
    rw [← Category.assoc, Over.w t]
  rw [hb, hc, φ.naturality]

/-- The overlap isomorphism of the descent datum defined by point-level overlap data. -/
def overlapIso : Descent.OverlapIso p ((baseChange p).obj G) :=
  isoOfPoints (overlapPoints φ) (fun t x => overlapPoints_naturality φ t x)

/-- Pulling the overlap isomorphism back along a map to the double overlap acts on
points by the corresponding value of the point-level overlap data. -/
theorem pullHom_overlapIso {T : Scheme.{u}} (q : T ⟶ Descent.Overlap p) {r s : T ⟶ S}
    (hr : q ≫ Descent.fst p = r) (hs : q ≫ Descent.snd p = s) (Z : Over T)
    (k : Z.left ⟶ B) (hrk : Z.hom ≫ r ≫ p = k) (hsk : Z.hom ≫ s ≫ p = k)
    (x : Z ⟶ ((baseChange r).obj ((baseChange p).obj G)).X) :
    iteratedPoints p G s Z k hsk
        (x ≫ (Descent.pullHom q hr hs (overlapIso φ).hom).hom.hom) =
      φ.toFun (Over.homMk (Z.hom ≫ r) (by simpa using hrk) : Over.mk k ⟶ cover p)
        (Over.homMk (Z.hom ≫ s) (by simpa using hsk))
        (iteratedPoints p G r Z k hrk x) := by
  subst hr hs
  have h1 : ((Over.map q).obj Z).hom ≫ Descent.fst p ≫ p = k := by
    simpa using hrk
  have h2 : ((Over.map q).obj Z).hom ≫ Descent.snd p ≫ p = k := by
    simpa using hsk
  let y := x ≫ (Descent.pullbackComparison (Descent.fst p) q _ rfl
    ((baseChange p).obj G)).inv.hom.hom
  have hx : x = y ≫ (Descent.pullbackComparison (Descent.fst p) q _ rfl
      ((baseChange p).obj G)).hom.hom.hom := by
    simp only [y, Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id]
    exact (Category.comp_id x).symm
  have hpull : x ≫ (Descent.pullHom q rfl rfl (overlapIso φ).hom).hom.hom =
      (y ≫ ((baseChange q).map (overlapIso φ).hom).hom.hom) ≫
        (Descent.pullbackComparison (Descent.snd p) q _ rfl
          ((baseChange p).obj G)).hom.hom.hom := by
    simp only [y, Descent.pullHom, Grp.comp_hom_hom, Category.assoc]
  rw [hpull, iteratedPoints_comparison p G (Descent.snd p) q _ rfl Z k hsk h2,
    baseChangePointsEquiv_comp]
  simp only [overlapIso, comp_isoOfPoints_hom]
  refine (iteratedPoints_overlapPoints φ ((Over.map q).obj Z) _ k h1 h2).trans ?_
  conv_rhs => rw [hx, iteratedPoints_comparison p G (Descent.fst p) q _ rfl Z k hrk h1]
  congr 1

/-- The overlap isomorphism built from point-level data satisfies the cocycle condition. -/
theorem overlapIso_cocycle : Descent.Cocycle (overlapIso φ) := by
  have h21 : Descent.p2 p ≫ p = Descent.p1 p ≫ p := by
    change (Descent.p12 p ≫ Descent.snd p) ≫ p = (Descent.p12 p ≫ Descent.fst p) ≫ p
    rw [Category.assoc, Category.assoc, ← pullback.condition]
  have h31 : Descent.p3 p ≫ p = Descent.p1 p ≫ p := by
    rw [← h21]
    change (Descent.p23 p ≫ Descent.snd p) ≫ p = Descent.p2 p ≫ p
    rw [Category.assoc, ← pullback.condition, Descent.p23_fst_assoc]
    exact (Category.assoc _ _ _).symm
  change Descent.pullHom (Descent.p12 p) rfl rfl (overlapIso φ).hom ≫
      Descent.pullHom (Descent.p23 p) (Descent.p23_fst p) rfl (overlapIso φ).hom =
    Descent.pullHom (Descent.p13 p) (Descent.p13_fst p) (Descent.p13_snd p) (overlapIso φ).hom
  apply hom_ext_points
  intro Z x
  have hk2 : Z.hom ≫ Descent.p2 p ≫ p = Z.hom ≫ Descent.p1 p ≫ p := by rw [h21]
  have hk3 : Z.hom ≫ Descent.p3 p ≫ p = Z.hom ≫ Descent.p1 p ≫ p := by rw [h31]
  apply (iteratedPoints p G (Descent.p3 p) Z _ hk3).injective
  rw [Grp.comp_hom_hom, ← Category.assoc x,
    pullHom_overlapIso φ (Descent.p23 p) (Descent.p23_fst p) rfl Z _ hk2 hk3,
    pullHom_overlapIso φ (Descent.p12 p) rfl rfl Z _ rfl hk2,
    pullHom_overlapIso φ (Descent.p13 p) (Descent.p13_fst p) (Descent.p13_snd p) Z _ rfl hk3,
    φ.cocycle]

/-- The actual descent datum on `p^*G` defined by point-level overlap data. -/
def pointDatum : Descent.Datum p ((baseChange p).obj G) where
  overlap := overlapIso φ
  cocycle := overlapIso_cocycle φ

variable {H : GroupScheme B} (ψ : (baseChange p).obj H ≅ (baseChange p).obj G)

/-- Points of `G` and of `H` over a test of `B` lifted to `S`, identified through an
isomorphism of their base changes to `S`. -/
def localPoints (V : Over S) (k : V.left ⟶ B) (h : V.hom ≫ p = k) :
    (Over.mk k ⟶ G.X) ≃* (Over.mk k ⟶ H.X) :=
  (baseChangePoints p G V k h).symm.trans
    ((pointsIso ψ.symm V).trans (baseChangePoints p H V k h))

theorem localPoints_apply (V : Over S) (k : V.left ⟶ B) (h : V.hom ≫ p = k)
    (z : Over.mk k ⟶ G.X) :
    localPoints ψ V k h z =
      baseChangePoints p H V k h ((baseChangePoints p G V k h).symm z ≫ ψ.inv.hom.hom) :=
  rfl

theorem localPoints_naturality {V V' : Over S} (t : V' ⟶ V)
    (k : V.left ⟶ B) (h : V.hom ≫ p = k) (k' : V'.left ⟶ B) (h' : V'.hom ≫ p = k')
    (τ : Over.mk k' ⟶ Over.mk k) (hτ : τ.left = t.left) (z : Over.mk k ⟶ G.X) :
    localPoints ψ V' k' h' (τ ≫ z) = τ ≫ localPoints ψ V k h z := by
  rw [localPoints_apply, localPoints_apply,
    baseChangePoints_symm_naturality p G t k h k' h' τ hτ, Category.assoc,
    baseChangePoints_naturality p H t k h k' h' τ hτ]

theorem localPoints_congr {Y : Scheme.{u}} {f f' : Y ⟶ S} (hf : f = f') (k : Y ⟶ B)
    (h : (Over.mk f).hom ≫ p = k) (h' : (Over.mk f').hom ≫ p = k) (z : Over.mk k ⟶ G.X) :
    localPoints ψ (Over.mk f) k h z = localPoints ψ (Over.mk f') k h' z := by
  subst hf
  rfl

/-- The local identifications along the two coordinates of the double overlap differ by
the point-level overlap data, when the identification of base changes is compatible with
the descent data. -/
theorem localPoints_overlap
    (hψ : Descent.Compatible (Descent.canonicalDatum p H) (pointDatum φ) ψ.hom)
    (W : Over (Descent.Overlap p)) (k : W.left ⟶ B)
    (h₁ : W.hom ≫ Descent.fst p ≫ p = k) (h₂ : W.hom ≫ Descent.snd p ≫ p = k)
    (z : Over.mk k ⟶ G.X) :
    localPoints ψ ((Over.map (Descent.snd p)).obj W) k (by simpa using h₂)
        (φ.toFun (firstPoint W.hom k h₁) (secondPoint W.hom k h₂) z) =
      localPoints ψ ((Over.map (Descent.fst p)).obj W) k (by simpa using h₁) z := by
  obtain ⟨v, rfl⟩ := (iteratedPoints p G (Descent.fst p) W k h₁).surjective z
  let u := v ≫ ((baseChange (Descent.fst p)).map ψ.inv).hom.hom
  have hu : u ≫ ((baseChange (Descent.fst p)).map ψ.hom).hom.hom = v :=
    comp_hom_comp_inv ((baseChange (Descent.fst p)).mapIso ψ.symm) v
  have hψ' : (baseChange (Descent.fst p)).map ψ.hom ≫ (overlapIso φ).hom =
      (Descent.canonicalOverlap p H).hom ≫ (baseChange (Descent.snd p)).map ψ.hom := hψ
  have hc : v ≫ (overlapIso φ).hom.hom.hom =
      (u ≫ (Descent.canonicalOverlap p H).hom.hom.hom) ≫
        ((baseChange (Descent.snd p)).map ψ.hom).hom.hom := by
    have := congrArg (fun f => u ≫ f.hom.hom) hψ'
    simp only [Grp.comp_hom_hom, ← Category.assoc] at this
    rw [hu] at this
    exact this
  have hφ : iteratedPoints p G (Descent.snd p) W k h₂ (v ≫ (overlapIso φ).hom.hom.hom) =
      φ.toFun (firstPoint W.hom k h₁) (secondPoint W.hom k h₂)
        (iteratedPoints p G (Descent.fst p) W k h₁ v) := by
    simp only [overlapIso, comp_isoOfPoints_hom]
    exact iteratedPoints_overlapPoints φ W v k h₁ h₂
  rw [← hφ, hc, iteratedPoints_map, localPoints_apply, MulEquiv.symm_apply_apply,
    comp_hom_comp_inv]
  change iteratedPoints p H (Descent.snd p) W k h₂
      (u ≫ (Descent.canonicalOverlap p H).hom.hom.hom) = _
  rw [iteratedPoints_canonicalOverlap p H W k h₁ h₂, iteratedPoints_map, localPoints_apply,
    show iteratedPoints p G (Descent.fst p) W k h₁ v =
      baseChangePoints p G ((Over.map (Descent.fst p)).obj W) k (by simpa using h₁)
        (baseChangePointsEquiv (Descent.fst p) ((baseChange p).obj G) W v) from rfl,
    MulEquiv.symm_apply_apply]

/-- The local isomorphisms from `G` to the descended group `H` on the points of the cover. -/
def solutionLocalIso : LocalGroupIso G H (cover p) where
  toFun {Z} b := localPoints ψ (Over.mk b.left) Z.hom (Over.w b)
  naturality {Z Z'} t b g := by
    let t' : Over.mk (t ≫ b).left ⟶ Over.mk b.left := Over.homMk t.left (by simp)
    exact localPoints_naturality ψ t' Z.hom (Over.w b) Z'.hom (Over.w (t ≫ b)) t rfl g

theorem solutionLocalIso_overlap
    (hψ : Descent.Compatible (Descent.canonicalDatum p H) (pointDatum φ) ψ.hom)
    {Z : Over B} (b c : Z ⟶ cover p) (g : Z ⟶ G.X) :
    (solutionLocalIso ψ).toFun c (φ.toFun b c g) = (solutionLocalIso ψ).toFun b g := by
  have hbc : b.left ≫ p = c.left ≫ p := (Over.w b).trans (Over.w c).symm
  let W : Over (Descent.Overlap p) := Over.mk (pullback.lift b.left c.left hbc)
  have h₁ : W.hom ≫ Descent.fst p ≫ p = Z.hom := by
    simp only [W, Over.mk_hom, pullback.lift_fst_assoc]
    exact Over.w b
  have h₂ : W.hom ≫ Descent.snd p ≫ p = Z.hom := by
    simp only [W, Over.mk_hom, pullback.lift_snd_assoc]
    exact Over.w c
  have hb : firstPoint W.hom Z.hom h₁ = b := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  have hc : secondPoint W.hom Z.hom h₂ = c := by
    apply Over.OverMorphism.ext
    exact pullback.lift_snd _ _ _
  have key := localPoints_overlap φ ψ hψ W Z.hom h₁ h₂ g
  rw [hb, hc] at key
  have e₁ := localPoints_congr ψ (pullback.lift_snd b.left c.left hbc) Z.hom
    (by simpa using Over.w c) (Over.w c) (φ.toFun b c g)
  have e₂ := localPoints_congr ψ (pullback.lift_fst b.left c.left hbc) Z.hom
    (by simpa using Over.w b) (Over.w b) g
  exact e₁.symm.trans (key.trans e₂)

end PointDescent

open PointDescent in
/-- **Existence of finite-Galois twisted forms.** -/
theorem finiteGaloisTwistExistence : FiniteGaloisTwistExistenceStatement.{u} := by
  intro K L _ _ _ _ _ A G hG a ξ
  let p : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  let φ : PointOverlap p G :=
    { toFun := fun b c => a.pointAut _ (ξ.toFun c b)
      naturality := fun t b c g => by
        change a.act (ξ.toFun (t ≫ c) (t ≫ b)) (t ≫ g) = t ≫ a.act (ξ.toFun c b) g
        rw [ξ.naturality, a.naturality]
      cocycle := fun b c d g => by
        change a.act (ξ.toFun d c) (a.act (ξ.toFun c b) g) = a.act (ξ.toFun d b) g
        rw [ξ.cocycle d c b, a.act_mul_left] }
  have := hG
  have hGL : IsAffineHom ((baseChange p).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom p)
    infer_instance
  obtain ⟨s, hs⟩ :=
    affineGroupSchemeFiniteGaloisObjectDescent K L ((baseChange p).obj G) hGL (pointDatum φ)
  refine ⟨s.obj, solutionLocalIso s.iso, hs, ?_⟩
  intro Z b c g
  exact solutionLocalIso_overlap φ s.iso s.compatible c b g

end Langlands.GroupScheme
