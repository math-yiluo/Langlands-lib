import Langlands.GroupScheme.Torus.EtalePermutationAtlasRefinement
import Langlands.GroupScheme.Descent.EtaleCoverHomDescent

/-! # Gluing comparisons between systems with the same local permutations -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.EtalePermutationAtlas

variable {S U U' V : Scheme.{u}} {D W : GroupScheme S}
  {I J : Type u} [Finite I] [Finite J]

/-- Coordinates of a pullback point are the coordinates of its original
projection under the corresponding point adjunction. -/
theorem coordinates_pullbackPoint (f : U ⟶ S)
    (d : (baseChange f).obj D ≅ splitTorus U I) (T : Over U)
    (x : T ⟶ ((baseChange f).obj D).X) :
    coordinates f d T.hom (x.left ≫ pullback.fst D.X.hom f)
      (by rw [Category.assoc, pullback.condition, ← Category.assoc]; exact congrArg (fun k => k ≫ f) (Over.w x)) =
      splitTorus.pointsEquiv I T (x ≫ d.hom.hom.hom) := by
  change splitTorus.pointsEquiv I T
    (((baseChangePointsEquiv f D T).symm (baseChangePointsEquiv f D T x)) ≫ d.hom.hom.hom) = _
  rw [MulEquiv.symm_apply_apply]

/-- Apply the comparison of two charts to an original-group point. -/
def comparisonPoint (f : U ⟶ S)
    (d : (baseChange f).obj D ≅ splitTorus U I)
    (w : (baseChange f).obj W ≅ splitTorus U I)
    {T : Scheme.{u}} (t : T ⟶ U) (x : T ⟶ D.X.left)
    (hx : x ≫ D.X.hom = t ≫ f) : Over.mk (t ≫ f) ⟶ W.X :=
  (chartPointsEquiv f w t).symm (coordinates f d t x hx)

@[simp]
theorem comparisonPoint_coordinates (f : U ⟶ S)
    (d : (baseChange f).obj D ≅ splitTorus U I)
    (w : (baseChange f).obj W ≅ splitTorus U I)
    {T : Scheme.{u}} (t : T ⟶ U) (x : T ⟶ D.X.left)
    (hx : x ≫ D.X.hom = t ≫ f) :
    coordinates f w t (comparisonPoint f d w t x hx).left (Over.w _) = coordinates f d t x hx :=
  (chartPointsEquiv f w t).apply_symm_apply _

/-- Equal base maps and equal original points give equal underlying comparison
points, independently of the displayed base equations. -/
theorem comparisonPoint_congr (f : U ⟶ S)
    (d : (baseChange f).obj D ≅ splitTorus U I)
    (w : (baseChange f).obj W ≅ splitTorus U I)
    {T : Scheme.{u}} {t t' : T ⟶ U} {x x' : T ⟶ D.X.left}
    (hx : x ≫ D.X.hom = t ≫ f) (hx' : x' ≫ D.X.hom = t' ≫ f)
    (ht : t = t') (hxx : x = x') :
    (comparisonPoint f d w t x hx).left = (comparisonPoint f d w t' x' hx').left := by
  subst t'; subst x'; rfl

/-- The comparison point is the projection of the actual local group
isomorphism applied to the actual pullback point. -/
theorem comparisonPoint_projection (f : U ⟶ S)
    (d : (baseChange f).obj D ≅ splitTorus U I)
    (w : (baseChange f).obj W ≅ splitTorus U I)
    {T : Scheme.{u}} (x : T ⟶ pullback D.X.hom f)
    (hx : (x ≫ pullback.fst D.X.hom f) ≫ D.X.hom = (x ≫ pullback.snd D.X.hom f) ≫ f) :
    (comparisonPoint f d w (x ≫ pullback.snd D.X.hom f)
        (x ≫ pullback.fst D.X.hom f) hx).left =
      x ≫ (d ≪≫ w.symm).hom.hom.hom.left ≫ pullback.fst W.X.hom f := by
  let T' : Over U := Over.mk (x ≫ pullback.snd D.X.hom f)
  let p : T' ⟶ ((baseChange f).obj D).X := Over.homMk x rfl
  have hc := coordinates_pullbackPoint f d T' p
  have he : comparisonPoint f d w T'.hom (p.left ≫ pullback.fst D.X.hom f) hx =
      baseChangePointsEquiv f W T' (p ≫ (d ≪≫ w.symm).hom.hom.hom) := by
    apply (chartPointsEquiv f w T'.hom).injective
    rw [comparisonPoint, MulEquiv.apply_symm_apply]
    rw [hc]
    change _ = splitTorus.pointsEquiv I T'
      (((baseChangePointsEquiv f W T').symm
        (baseChangePointsEquiv f W T' (p ≫ (d ≪≫ w.symm).hom.hom.hom))) ≫ w.hom.hom.hom)
    rw [MulEquiv.symm_apply_apply]
    simp only [Iso.trans_hom, Iso.symm_hom, Grp.comp_hom_hom, Category.assoc]
    have hw : w.inv.hom.hom ≫ w.hom.hom.hom = 𝟙 _ := by
      exact congrArg (fun a : splitTorus U I ⟶ splitTorus U I => a.hom.hom) w.inv_hom_id
    rw [hw, Category.comp_id]
  exact congrArg Over.Hom.left he

/-- Comparisons between two chart systems agree wherever both systems obey
the same permutation on every test. -/
theorem comparisonPoint_eq_of_agreeBy (f : U ⟶ S) (g : U' ⟶ S)
    (d : (baseChange f).obj D ≅ splitTorus U I)
    (d' : (baseChange g).obj D ≅ splitTorus U' J)
    (w : (baseChange f).obj W ≅ splitTorus U I)
    (w' : (baseChange g).obj W ≅ splitTorus U' J)
    (q : V ⟶ U) (q' : V ⟶ U') (r : V ⟶ S)
    (h : q ≫ f = r) (h' : q' ≫ g = r) (σ : J ≃ I)
    (Hd : AgreeBy f g d d' q q' r h h' σ)
    (Hw : AgreeBy f g w w' q q' r h h' σ)
    (T : Over V) (x : T.left ⟶ D.X.left) (hx : x ≫ D.X.hom = T.hom ≫ r) :
    (comparisonPoint f d w (T.hom ≫ q) x (by rw [Category.assoc, h]; exact hx)).left =
      (comparisonPoint g d' w' (T.hom ≫ q') x (by rw [Category.assoc, h']; exact hx)).left := by
  let y := comparisonPoint f d w (T.hom ≫ q) x (by rw [Category.assoc, h]; exact hx)
  let z := comparisonPoint g d' w' (T.hom ≫ q') x (by rw [Category.assoc, h']; exact hx)
  have hy : y.left ≫ W.X.hom = T.hom ≫ r := by
    have hy0 : y.left ≫ W.X.hom = (T.hom ≫ q) ≫ f := Over.w y
    exact hy0.trans (by simp only [Category.assoc, h])
  have hz : y.left ≫ W.X.hom = (T.hom ≫ q') ≫ g := by
    exact hy.trans (by simp only [Category.assoc, h'])
  have hc : coordinates g w' (T.hom ≫ q') y.left hz =
      coordinates g w' (T.hom ≫ q') z.left (Over.w z) := by
    funext j
    rw [Hw.coordinates f g w w' q q' r h h' σ T y.left hy j]
    rw [comparisonPoint_coordinates, comparisonPoint_coordinates]
    exact (Hd.coordinates f g d d' q q' r h h' σ T x hx j).symm
  have he : (Over.homMk y.left hz : Over.mk ((T.hom ≫ q') ≫ g) ⟶ W.X) = z :=
    (chartPointsEquiv g w' (T.hom ≫ q')).injective hc
  exact congrArg Over.Hom.left he

end Langlands.GroupScheme.EtalePermutationAtlas

namespace Langlands.GroupScheme.EtalePermutationAtlas

variable {S U : Scheme.{u}} {D W : GroupScheme S} {I : Type u} [Finite I]

/-- A specified lift of the original point computes the same chart comparison. -/
theorem comparisonPoint_projection_of_lift (f : U ⟶ S)
    (d : (baseChange f).obj D ≅ splitTorus U I)
    (w : (baseChange f).obj W ≅ splitTorus U I)
    {T : Scheme.{u}} (p : T ⟶ pullback D.X.hom f) (t : T ⟶ U)
    (x : T ⟶ D.X.left) (hx : x ≫ D.X.hom = t ≫ f)
    (ht : p ≫ pullback.snd D.X.hom f = t) (hp : p ≫ pullback.fst D.X.hom f = x) :
    (comparisonPoint f d w t x hx).left =
      p ≫ (d ≪≫ w.symm).hom.hom.hom.left ≫ pullback.fst W.X.hom f := by
  have hpb : (p ≫ pullback.fst D.X.hom f) ≫ D.X.hom =
      (p ≫ pullback.snd D.X.hom f) ≫ f := by rw [Category.assoc, pullback.condition, Category.assoc]
  exact (comparisonPoint_congr f d w hx hpb ht.symm hp.symm).trans
    (comparisonPoint_projection f d w p hpb)

variable (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
  (I : 𝒰.I₀ → Type u) [∀ i, Finite (I i)]
  (d : ∀ i, (baseChange (𝒰.f i)).obj D ≅ splitTorus (𝒰.X i) (I i))
  (w : ∀ i, (baseChange (𝒰.f i)).obj W ≅ splitTorus (𝒰.X i) (I i))

/-- The two actual chart systems obey the same locally constant permutations. -/
def SameLocalPermutations : Prop :=
  ∀ i j (z : (pullback (𝒰.f i) (𝒰.f j) : Scheme.{u})),
    ∃ (O : (pullback (𝒰.f i) (𝒰.f j)).Opens) (_ : z ∈ O) (σ : I j ≃ I i),
      AgreeBy (𝒰.f i) (𝒰.f j) (d i) (d j)
        (O.ι ≫ pullback.fst (𝒰.f i) (𝒰.f j)) (O.ι ≫ pullback.snd (𝒰.f i) (𝒰.f j))
        (O.ι ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)
        (by simp only [Category.assoc]) (by simp only [Category.assoc, pullback.condition]) σ ∧
      AgreeBy (𝒰.f i) (𝒰.f j) (w i) (w j)
        (O.ι ≫ pullback.fst (𝒰.f i) (𝒰.f j)) (O.ι ≫ pullback.snd (𝒰.f i) (𝒰.f j))
        (O.ι ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)
        (by simp only [Category.assoc]) (by simp only [Category.assoc, pullback.condition]) σ

/-- Matching local permutations give all-test compatibility of the actual
chart-comparison homomorphisms. -/
theorem SameLocalPermutations.compatible (H : SameLocalPermutations 𝒰 I d w) :
    Descent.EtaleCoverHomDescent.Compatible 𝒰 (fun i => (d i ≪≫ (w i).symm).hom) := by
  intro Z i j x y hxy
  let m : Z ⟶ pullback (𝒰.f i) (𝒰.f j) := pullback.lift
    (x ≫ pullback.snd D.X.hom (𝒰.f i)) (y ≫ pullback.snd D.X.hom (𝒰.f j)) (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hxy,
        Category.assoc, pullback.condition, ← Category.assoc])
  apply Scheme.hom_ext_of_forall
  intro z
  obtain ⟨O, hz, σ, Hd, Hw⟩ := H i j (m z)
  let P : Z.Opens := m ⁻¹ᵁ O
  let k : (P : Scheme.{u}) ⟶ (O : Scheme.{u}) :=
    IsOpenImmersion.lift O.ι (P.ι ≫ m) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      exact p.2)
  have hk : k ≫ O.ι = P.ι ≫ m := IsOpenImmersion.lift_fac _ _ _
  refine ⟨P, hz, ?_⟩
  let xp := P.ι ≫ x
  let yp := P.ι ≫ y
  let xd := xp ≫ pullback.fst D.X.hom (𝒰.f i)
  have ht : xp ≫ pullback.snd D.X.hom (𝒰.f i) =
      k ≫ (O.ι ≫ pullback.fst (𝒰.f i) (𝒰.f j)) := by
    rw [← Category.assoc, hk]
    simp only [xp, Category.assoc, m, pullback.lift_fst]
  have ht' : yp ≫ pullback.snd D.X.hom (𝒰.f j) =
      k ≫ (O.ι ≫ pullback.snd (𝒰.f i) (𝒰.f j)) := by
    rw [← Category.assoc, hk]
    simp only [yp, Category.assoc, m, pullback.lift_snd]
  have hp' : yp ≫ pullback.fst D.X.hom (𝒰.f j) = xd := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun t => P.ι ≫ t) hxy.symm).trans (Category.assoc _ _ _).symm)
  have hx : xd ≫ D.X.hom = k ≫ (O.ι ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) := by
    change (xp ≫ pullback.fst D.X.hom (𝒰.f i)) ≫ D.X.hom = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht]
    simp only [Category.assoc]
  have hxa : xd ≫ D.X.hom = (k ≫ (O.ι ≫ pullback.fst (𝒰.f i) (𝒰.f j))) ≫ 𝒰.f i :=
    hx.trans (Category.assoc _ _ _).symm
  have hxb : xd ≫ D.X.hom = (k ≫ (O.ι ≫ pullback.snd (𝒰.f i) (𝒰.f j))) ≫ 𝒰.f j := by
    exact hx.trans (by simp only [Category.assoc, pullback.condition])
  have hc := comparisonPoint_eq_of_agreeBy (𝒰.f i) (𝒰.f j) (d i) (d j) (w i) (w j)
    (O.ι ≫ pullback.fst (𝒰.f i) (𝒰.f j)) (O.ι ≫ pullback.snd (𝒰.f i) (𝒰.f j))
    (O.ι ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) _ _ σ Hd Hw (Over.mk k) xd hx
  have hpa := comparisonPoint_projection_of_lift (𝒰.f i) (d i) (w i) xp _ xd hxa ht rfl
  have hpb := comparisonPoint_projection_of_lift (𝒰.f j) (d j) (w j) yp _ xd hxb ht' hp'
  simpa only [xp, yp, Category.assoc] using hpa.symm.trans (hc.trans hpb)

/-- Matching permutations are symmetric between the two chart systems. -/
theorem SameLocalPermutations.symm (H : SameLocalPermutations 𝒰 I d w) :
    SameLocalPermutations 𝒰 I w d := by
  intro i j z
  obtain ⟨O, hz, σ, Hd, Hw⟩ := H i j z
  exact ⟨O, hz, σ, Hw, Hd⟩

/-- The actual global group-scheme isomorphism obtained from matching split
charts on a small étale cover. -/
def matchingChartsIso (H : SameLocalPermutations 𝒰 I d w) : D ≅ W :=
  Descent.EtaleCoverHomDescent.iso 𝒰 (fun i => d i ≪≫ (w i).symm)
    H.compatible H.symm.compatible

@[simp]
theorem baseChange_matchingChartsIso (H : SameLocalPermutations 𝒰 I d w) (i : 𝒰.I₀) :
    (baseChange (𝒰.f i)).mapIso (matchingChartsIso 𝒰 I d w H) = d i ≪≫ (w i).symm :=
  Descent.EtaleCoverHomDescent.baseChange_iso 𝒰 (fun i => d i ≪≫ (w i).symm)
    H.compatible H.symm.compatible i

end Langlands.GroupScheme.EtalePermutationAtlas
