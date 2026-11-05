import Langlands.GroupScheme.Rational.SplitUnipotentRationalDetection
import Langlands.GroupScheme.Reductive.SplitNormalFppfProductProof
import Langlands.GroupScheme.Reductive.SplitUnipotentRadicalMaximal

/-! # Split closed subgroups of commutative groups containing images of split groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RationalDensity

open Langlands.AlgebraicGeometry.PointTopology RelativeRoot BorelExistence

variable {k : Type u} [Field k]

/-- A closed subgroup which is smooth, connected and split unipotent. -/
structure IsSplitClosed {I G : GroupScheme (Spec (CommRingCat.of k))} (κ : I ⟶ G) : Prop where
  isClosedSubgroup : IsClosedSubgroup κ
  smooth : Smooth I.X.hom
  connectedSpace : ConnectedSpace I.X.left
  isSplitUnipotent : IsSplitUnipotent I

/-- The unit inclusion is a split closed subgroup. -/
theorem trivial_isSplitClosed (G : GroupScheme (Spec (CommRingCat.of k))) :
    IsSplitClosed (0 : Grp.trivial (Over (Spec (CommRingCat.of k))) ⟶ G) :=
  have h := SplitUnipotentRadicalExistence.trivial_isSplitCandidate G
  ⟨h.isClosedSubgroup, h.smooth, h.connectedSpace, h.isSplitUnipotent⟩

set_option backward.isDefEq.respectTransparency false in
/-- In a smooth affine commutative group, a split closed subgroup and the image of a
homomorphism from a smooth connected affine split group lie in a common split closed
subgroup. -/
theorem IsSplitClosed.exists_enlarge {G I S : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hG : ∀ (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ G.X), a * b = b * a)
    {κ : I ⟶ G} (hκ : IsSplitClosed κ)
    [Smooth S.X.hom] [ConnectedSpace S.X.left] [IsAffineHom S.X.hom]
    (hS : IsSplitUnipotent S) (φ : S ⟶ G) :
    ∃ (D : GroupScheme (Spec (CommRingCat.of k))) (inc : D ⟶ G) (j₀ : I ⟶ D) (i₀ : S ⟶ D),
      IsSplitClosed inc ∧ j₀ ≫ inc = κ ∧ i₀ ≫ inc = φ := by
  have : Smooth I.X.hom := hκ.smooth
  have : ConnectedSpace I.X.left := hκ.connectedSpace
  have : IsClosedImmersion κ.hom.hom.left := hκ.isClosedSubgroup
  have : Mono κ.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom I.X.hom := by
    rw [← Over.w κ.hom.hom]
    infer_instance
  have : GeometricallyConnected I.X.hom := geometricallyConnected_of_connected I
  have hN : (SubgroupFunctor.range κ).IsNormal := by
    intro T g x _ hx
    rw [hG T g x, mul_inv_cancel_right]
    exact hx
  -- the semidirect product `I ⋊ S` and its image `D` in `G`
  let hc : Semidirect.ConjStable φ κ := Semidirect.conjStable_of_isNormal φ κ hN
  have hAs : Smooth (Semidirect.group hc).X.hom :=
    show Smooth (pullback.fst I.X.hom S.X.hom ≫ I.X.hom) by infer_instance
  have : IsAffineHom (pullback.fst I.X.hom S.X.hom) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have hAa : IsAffineHom (Semidirect.group hc).X.hom :=
    show IsAffineHom (pullback.fst I.X.hom S.X.hom ≫ I.X.hom) by infer_instance
  have hAc : ConnectedSpace (Semidirect.group hc).X.left :=
    show ConnectedSpace ↥(Limits.pullback I.X.hom S.X.hom) by infer_instance
  have hIm := SplitNormalFppfProduct.homImageHypothesis k
  obtain ⟨D, inc, fac, hinc, hfac, -, hsu, -, hDs, hDc, hDa⟩ :=
    hIm _ G (Semidirect.mulHom hc) hAs hAc hAa inferInstance inferInstance
  have : IsClosedImmersion inc.hom.hom.left := hinc
  have : Mono inc.hom.hom := Over.mono_of_mono_left _
  have : Smooth D.X.hom := hDs
  have : ConnectedSpace D.X.left := hDc
  have : IsAffineHom D.X.hom := hDa
  have : Surjective fac.hom.hom.left := hsu
  have hfac' : fac.hom.hom ≫ inc.hom.hom = Semidirect.mulMap hc := by
    rw [← Grp.comp_hom_hom, hfac]
    exact Semidirect.mulHom_hom_hom hc
  -- `I` and `S` inside `D`
  let j₀ : I.X ⟶ D.X := (Semidirect.conjAction hc).inl ≫ fac.hom.hom
  have hj₀ : j₀ ≫ inc.hom.hom = κ.hom.hom := by
    rw [Category.assoc, hfac', Semidirect.inl_mulMap]
  let i₀ : S.X ⟶ D.X := (Semidirect.conjAction hc).inr ≫ fac.hom.hom
  have hi₀ : i₀ ≫ inc.hom.hom = φ.hom.hom := by
    rw [Category.assoc, hfac', Semidirect.inr_mulMap]
  have : IsMonHom j₀ := SplitSemidirect.isMonHom_of_comp_eq inc j₀ κ.hom.hom hj₀
  have : IsMonHom i₀ := SplitSemidirect.isMonHom_of_comp_eq inc i₀ φ.hom.hom hi₀
  let j' : I ⟶ D := Grp.homMk j₀
  let i' : S ⟶ D := Grp.homMk i₀
  have hj' : IsClosedSubgroup j' := by
    have : IsClosedImmersion (j₀.left ≫ inc.hom.hom.left) := by
      rw [← Over.comp_left, hj₀]
      infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion j₀.left inc.hom.hom.left
  have hN' : (SubgroupFunctor.range j').IsNormal := by
    intro T g x _ hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    refine SubgroupFunctor.mem_range.mpr ⟨y, ?_⟩
    apply (cancel_mono inc.hom.hom).mp
    change (y ≫ j₀) ≫ inc.hom.hom = (g * (y ≫ j₀) * g⁻¹) ≫ inc.hom.hom
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hG T (g ≫ inc.hom.hom),
      mul_inv_cancel_right]
  have hsurj' : Surjective (SplitSemidirect.mulPoints j' i').left := by
    have he : SplitSemidirect.mulPoints j' i' = fac.hom.hom := by
      apply (cancel_mono inc.hom.hom).mp
      change ((fst I.X S.X ≫ j₀) * (snd I.X S.X ≫ i₀)) ≫ inc.hom.hom = _
      rw [MonObj.mul_comp, Category.assoc (fst I.X S.X) j₀, hj₀, Category.assoc (snd I.X S.X) i₀,
        hi₀, hfac']
      rfl
    rw [he]
    infer_instance
  obtain ⟨n, hn⟩ := hS
  have hDsplit := SplitSemidirect.isSplitUnipotent_of_surjective hIm n j' i' hj' hN'
    hκ.isSplitUnipotent hn hsurj'
  refine ⟨D, inc, j', i', ⟨hinc, hDs, hDc, hDsplit⟩, ?_, ?_⟩
  · exact Grp.hom_ext _ _ hj₀
  · exact Grp.hom_ext _ _ hi₀

/-- In a smooth affine commutative group, a morphism `Y ⊗ S ⟶ G` which restricts to a
homomorphism on every rational fibre `{y} × S`, with `S` smooth connected affine and split,
factors through a split closed subgroup as soon as rational points detect functions on
`Y ⊗ S`. -/
theorem exists_splitClosed_factor {G S : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hG : ∀ (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ G.X), a * b = b * a)
    [Smooth S.X.hom] [ConnectedSpace S.X.left] [IsAffineHom S.X.hom]
    (hS : IsSplitUnipotent S) {Y : Over (Spec (CommRingCat.of k))} (ω : Y ⊗ S.X ⟶ G.X)
    (hdet : RationalPointsDetectFunctions (Y ⊗ S.X))
    (hφ : ∀ y : RationalPoint k Y, ∃ φ : S ⟶ G, pointSection S.X y ≫ ω = φ.hom.hom) :
    ∃ (I : GroupScheme (Spec (CommRingCat.of k))) (κ : I ⟶ G), IsSplitClosed κ ∧
      ∃ g : Y ⊗ S.X ⟶ I.X, g ≫ κ.hom.hom = ω := by
  classical
  -- a split closed subgroup of minimal coordinate-kernel height
  let P : ℕ → Prop := fun n => ∃ (I : GroupScheme (Spec (CommRingCat.of k))) (κ : I ⟶ G),
    IsSplitClosed κ ∧ (coordinateKernel κ).height.toNat = n
  have hP : ∃ n, P n := ⟨_, Grp.trivial _, 0, trivial_isSplitClosed G, rfl⟩
  obtain ⟨I, κ, hκ, hheight⟩ := Nat.find_spec hP
  have hmin : ∀ (D : GroupScheme (Spec (CommRingCat.of k))) (inc : D ⟶ G), IsSplitClosed inc →
      (coordinateKernel κ).height ≤ (coordinateKernel inc).height := by
    intro D inc hinc
    have := hκ.smooth
    have := hκ.connectedSpace
    have := hinc.smooth
    have := hinc.connectedSpace
    have h1 : (coordinateKernel κ).height.toNat ≤ (coordinateKernel inc).height.toNat := by
      rw [hheight]
      exact Nat.find_min' hP ⟨D, inc, hinc, rfl⟩
    rw [← ENat.natCast_toNat (coordinateKernel_height_ne_top κ),
      ← ENat.natCast_toNat (coordinateKernel_height_ne_top inc)]
    exact_mod_cast h1
  -- by minimality, every homomorphism from `S` factors through `κ`
  have hfac : ∀ φ : S ⟶ G, ∃ ψ : S ⟶ I, ψ ≫ κ = φ := by
    intro φ
    obtain ⟨D, inc, j₀, i₀, hinc, hj, hi⟩ := hκ.exists_enlarge hG hS φ
    have := hinc.smooth
    have := hinc.connectedSpace
    have : IsIso j₀ := isIso_of_coordinateKernel_height_le κ inc j₀ hκ.isClosedSubgroup
      hinc.isClosedSubgroup hj (hmin D inc hinc)
    exact ⟨i₀ ≫ inv j₀, by rw [Category.assoc, ← hj, IsIso.inv_hom_id_assoc, hi]⟩
  have : IsClosedImmersion κ.hom.hom.left := hκ.isClosedSubgroup
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨l, hl⟩ := RationalPointsDetectFunctions.exists_factor hdet κ.hom.hom ω (fun x => by
    obtain ⟨φ, hφx⟩ := hφ (x ≫ fst Y S.X)
    obtain ⟨ψ, hψ⟩ := hfac φ
    refine ⟨(x ≫ snd Y S.X) ≫ ψ.hom.hom, ?_⟩
    have hx : x = (x ≫ snd Y S.X) ≫ pointSection S.X (x ≫ fst Y S.X) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, pointSection_fst, ← Category.assoc,
          toUnit_unique ((x ≫ snd Y S.X) ≫ toUnit S.X) (𝟙 _), Category.id_comp]
      · rw [Category.assoc, pointSection_snd, Category.comp_id]
    rw [Category.assoc, ← Grp.comp_hom_hom, hψ, ← hφx, ← Category.assoc, ← hx])
  exact ⟨I, κ, hκ, l, hl⟩

end Langlands.GroupScheme.RationalDensity
