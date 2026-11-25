import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimpleIrreducibleStatement
import Langlands.GroupScheme.Reductive.LinkedRootsAlmostSimple
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.RootDatumRationalBase
import Langlands.GroupScheme.Rational.RelativeRootSystemIrreducibleProof
import Langlands.GroupScheme.Rational.QuasiSplitSplittingReduction
import Langlands.GroupScheme.Derived.SemisimplePerfectReduction
import Langlands.GroupScheme.AlgebraicFundamentalGroupWeyl
import Langlands.GroupScheme.Rational.SplitTorusRationalDetection

/-! # Absolute almost-simplicity is irreducibility of the absolute root system

Conrad, *Reductive group schemes*, Corollary 5.1.18. For a semisimple group `G` over a field
`k` with a maximal torus `i` of `G_{k̄}`, `G` is absolutely almost simple exactly when the
rational root system of `(G_{k̄}, i)` is irreducible.

The direction `⇒` is the published irreducibility of the relative root system of an
almost-simple group, applied over `k̄`. For `⇐`, a smooth connected closed normal subgroup
`H` of `G_{k̄}` splits the roots into those whose root groups lie in `H` and those whose root
groups centralize `H` (the normal-root dichotomy). The rank-one relation shows that a root
group commuting with both root groups `U_{±β}` has character trivial on the coroot `β^∨`, so
the two classes are orthogonal. Irreducibility then forces one class to be empty.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

namespace RootPairNoncommutation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} {J : Type u}

/-- **Commuting root groups and coroot pairings.** Let `β = P.root r` and `β' = P.root r'` be
roots of a split maximal torus of a connected reductive group, with root datum `P`. If on a
test scheme `Z` every point of `U_β` commutes with every point of `U_β'` and of `U_{-β'}`, then
`v ^ ⟨β, β'^∨⟩ = 1` for every unit `v = 1 + c` of `Γ(Z)`. The point `x_β(1)` commutes with
`β'^∨(v)`, which the rank-one relation writes through `U_{±β'}`, and conjugation by `β'^∨(v)`
scales `x_β(1)` to `x_β(v ^ ⟨β, β'^∨⟩)`. -/
theorem zpow_pairing_eq_one_of_commute (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) {i : T.toGrp ⟶ G} (hi : IsMaximalTorus i)
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)} (hP : IsRootDatumOf i P)
    (r r' : J) {Z : Over (Spec (CommRingCat.of k))}
    (hcomm : ∀ x ∈ (RelativeRoot.subgroup i (P.root r)).carrier Z,
      ∀ y, (y ∈ (RelativeRoot.subgroup i (P.root r')).carrier Z ∨
        y ∈ (RelativeRoot.subgroup i (-P.root r')).carrier Z) → Commute x y)
    (c : Γ(Z.left, ⊤)) (hu : IsUnit (1 + c)) :
    hu.unit ^ P.pairing r r' = 1 := by
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨xp, -, hxpm, -, hxp, -, -⟩ :=
    exists_monic_rootRankOneRelations hG hT i hi P hP r
  obtain ⟨yp, ym, hypm, hymm, hyp, hym, hrel⟩ :=
    exists_monic_rootRankOneRelations hG hT i hi P hP r'
  have hroot (s : J) : P.root s ∈ roots i := hP.2.1 ▸ Set.mem_range_self s
  obtain ⟨s', hs'⟩ : -P.root r' ∈ Set.range P.root :=
    P.neg_mem_range_root_iff.mpr (Set.mem_range_self r')
  have hneg : -P.root r' ∈ roots i := hs' ▸ hroot s'
  have hnegHigh : RelativeRoot.HasNoHigherRoots i (-P.root r') :=
    hs' ▸ hasNoHigherRoots hG hT hi hP s'
  have hxrep := hxp.represents_root hG hT hi (hroot r) (hasNoHigherRoots hG hT hi hP r)
  have hyprep := hyp.represents_root hG hT hi (hroot r') (hasNoHigherRoots hG hT hi hP r')
  have hymrep := hym.represents_root hG hT hi hneg hnegHigh
  let x : Z ⟶ G.X := RootCell.pt 1 ≫ xp.hom.hom
  have hx : x ∈ (RelativeRoot.subgroup i (P.root r)).carrier Z :=
    mem_of_isRepresentedBy hxrep _
  have hm : ∀ b : Γ(Z.left, ⊤), Commute x (RootCell.pt b ≫ ym.hom.hom) := fun b =>
    hcomm x hx _ (Or.inr (mem_of_isRepresentedBy hymrep _))
  have hp : ∀ b : Γ(Z.left, ⊤), Commute x (RootCell.pt b ≫ yp.hom.hom) := fun b =>
    hcomm x hx _ (Or.inl (mem_of_isRepresentedBy hyprep _))
  -- The rank-one relation for `β'` at `X = 1`, `Y = c`.
  let v : Γ(Z.left, ⊤)ˣ := hu.unit
  have hv : (v : Γ(Z.left, ⊤)) = 1 + c := hu.unit_spec
  let t : Z ⟶ T.X :=
    (Gm.pointsEquiv _ Z).symm v ≫ (CommGroupScheme.groupHom (P.coroot r')).hom.hom
  let w : Γ(Z.left, ⊤) := ((v⁻¹ : Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤))
  have hrelZ := hrel Z (RootCell.pt 1) (RootCell.pt c) (RootCell.pt (w * 1))
    (RootCell.pt (w * c)) v (by rw [RootCell.crd_pt, RootCell.crd_pt, one_mul, hv])
    (by rw [RootCell.crd_pt, RootCell.crd_pt]) (by rw [RootCell.crd_pt, RootCell.crd_pt])
  change _ = _ * (t ≫ i.hom.hom) * _ at hrelZ
  have ht := solve_middle hrelZ
  have hcomm' : Commute x (t ≫ i.hom.hom) := by
    rw [ht]
    exact (((hm _).inv_right.mul_right ((hp _).mul_right (hm _))).mul_right (hp _).inv_right)
  -- The torus point `β'^∨(v)` scales the `β`-coordinate by `v ^ ⟨β, β'^∨⟩`.
  have heq := hxp Z t 1
  have hval : VectorGroup.charValue (P.root r) Z t =
      ((v ^ P.pairing r r' : Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) := by
    rw [RankOneRootCellRelation.charValue_eq_cu, cu_cocharacter, ← hP.1,
      P.root_coroot_eq_pairing]
  have hx1 : (t ≫ i.hom.hom) * x * (t ≫ i.hom.hom)⁻¹ = x := by
    rw [hcomm'.eq.symm, mul_inv_cancel_right]
  change (t ≫ i.hom.hom) * x * (t ≫ i.hom.hom)⁻¹ = _ at heq
  rw [hx1, hval, mul_one] at heq
  have hpt : (RootCell.pt (1 : Γ(Z.left, ⊤)) : Z ⟶ (RootCell.Ga k).X) =
      RootCell.pt ((v ^ P.pairing r r' : Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) :=
    (cancel_mono xp.hom.hom).1 heq
  have h1 := congrArg RootCell.crd hpt
  rw [RootCell.crd_pt, RootCell.crd_pt] at h1
  exact Units.val_eq_one.mp h1.symm

/-- **Commuting root groups are orthogonal.** Over an infinite field, if on every test scheme
every point of `U_β` commutes with every point of `U_β'` and of `U_{-β'}`, then
`⟨β, β'^∨⟩ = 0`. -/
theorem pairing_eq_zero_of_commute [Infinite k] (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) {i : T.toGrp ⟶ G} (hi : IsMaximalTorus i)
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)} (hP : IsRootDatumOf i P)
    (r r' : J)
    (hcomm : ∀ Z : Over (Spec (CommRingCat.of k)),
      ∀ x ∈ (RelativeRoot.subgroup i (P.root r)).carrier Z,
      ∀ y, (y ∈ (RelativeRoot.subgroup i (P.root r')).carrier Z ∨
        y ∈ (RelativeRoot.subgroup i (-P.root r')).carrier Z) → Commute x y) :
    P.pairing r r' = 0 := by
  let Z : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 (Spec (CommRingCat.of k)))
  let φ : k ≃+* Γ(Z.left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  apply splitTorus.eq_zero_of_forall_units_zpow_eq_one (k := k)
  intro u
  have hu : IsUnit (1 + φ ((u : k) - 1)) := by
    rw [← map_one φ, ← map_add, add_sub_cancel]
    exact u.isUnit.map φ
  have h := zpow_pairing_eq_one_of_commute hG hT hi hP r r' (hcomm Z) (φ ((u : k) - 1)) hu
  have hmap : Units.map φ.toMonoidHom u = hu.unit := by
    apply Units.ext
    rw [Units.coe_map, IsUnit.unit_spec, ← map_one φ, ← map_add, add_sub_cancel]
    rfl
  apply Units.map_injective (f := φ.toMonoidHom) φ.injective
  rw [map_zpow, hmap, h, map_one]

/-- Points of one root subgroup commute: no positive multiple `n β`, `n ≥ 2`, is a root. -/
theorem commute_of_mem_same_root (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) {i : T.toGrp ⟶ G} (hi : IsMaximalTorus i)
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)} (hP : IsRootDatumOf i P)
    (r : J) {Z : Over (Spec (CommRingCat.of k))} {x y : Z ⟶ G.X}
    (hx : x ∈ (RelativeRoot.subgroup i (P.root r)).carrier Z)
    (hy : y ∈ (RelativeRoot.subgroup i (P.root r)).carrier Z) : Commute x y := by
  let : Smooth G.X.hom := hG.smooth
  have hroot : P.root r ∈ roots i := hP.2.1 ▸ Set.mem_range_self r
  have hhigh := hasNoHigherRoots hG hT hi hP r
  let : HasUniqueDiv (ℚ ⊗[ℤ] characterLattice T) := HasUniqueDiv.of_module_rat _
  let : HasUniqueDiv (characterLattice T) :=
    hT.character_toRat_injective.hasUniqueDiv toRat
  refine commute_of_no_strict_combinations hT i (P.root r) (P.root r) hroot.1 hroot.1
    (fun n m hn hm => ?_) hx hy
  rw [← add_smul]
  refine ⟨fun h0 => hroot.1 (nsmul_right_injective (by omega : n + m ≠ 0)
    (h0.trans (smul_zero _).symm)), ?_⟩
  rw [← relativeRoots_eq_roots]
  exact hhigh (n + m) (by omega)

end RootPairNoncommutation

section Irreducible

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The coroot functional of a root pairing with the full actual-root image is the rational
extension of the integral coroot of a root datum, at the same root. Both reflections preserve
the finite spanning set of actual root vectors (Bourbaki's uniqueness lemma). -/
theorem coroot'_eq_corootFunctional [LocallyOfFiniteType G.X.hom]
    {t : T.toGrp ⟶ G} [Mono t.hom.hom.left] (hT : IsSplitTorus T.toGrp)
    {J' : Type*} {PZ : RootDatum J' (characterLattice T) (cocharacterLattice T)}
    (hPZ : IsRootDatumOf t PZ)
    {J W : Type*} [AddCommGroup W] [Module ℚ W]
    (P : RootPairing J ℚ (relativeRootSpan t) W)
    (hP : Subtype.val '' Set.range P.root = toRat '' relativeRoots t)
    (j : J) (r : J') (hjr : toRat (PZ.root r) = (P.root j).val) :
    P.coroot' j = RelativeRootSystem.corootFunctional t (PZ.coroot r) := by
  have hfinite : (relativeRoots t).Finite := hT.finite_relativeRoots t
  have hrange : Set.range P.root = Set.range (RelativeRootSystem.rootVector t) := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      have hmem : (P.root m).val ∈ toRat '' relativeRoots t :=
        hP ▸ ⟨P.root m, ⟨m, rfl⟩, rfl⟩
      obtain ⟨β, hβ, hβm⟩ := hmem
      exact ⟨⟨β, hβ⟩, Subtype.ext hβm⟩
    · rintro ⟨β, rfl⟩
      have hmem : toRat β.val ∈ Subtype.val '' Set.range P.root :=
        hP ▸ ⟨β.val, β.property, rfl⟩
      obtain ⟨y, ⟨m, rfl⟩, hy⟩ := hmem
      exact ⟨m, Subtype.ext hy⟩
  have hfin : (Set.range P.root).Finite := by
    rw [hrange]
    have := hfinite.to_subtype
    exact Set.finite_range _
  have hspan : Submodule.span ℚ (Set.range P.root) = ⊤ :=
    rootSpan_eq_top_of_full_relativeRoot_image t P hP
  let D := hPZ.relativeRootReflectionData
  let α : relativeRoots t := hPZ.relativeRootEquiv r
  have hαj : RelativeRootSystem.rootVector t α = P.root j := Subtype.ext hjr
  have hD : D.coroot α = PZ.coroot r := by
    change PZ.coroot (hPZ.relativeRootIndex (hPZ.relativeRootEquiv r)) = _
    rw [hPZ.relativeRootIndex_relativeRootEquiv]
  have hg : RelativeRootSystem.corootFunctional t (PZ.coroot r) (P.root j) = 2 := by
    rw [← hαj, RelativeRootSystem.corootFunctional_rootVector, hPZ.relativeRootEquiv_val,
      ← hPZ.1, PZ.root_coroot_two]
    norm_num
  have hgmaps := D.mapsTo_preReflection α
  rw [hαj, hD, ← hrange] at hgmaps
  refine Module.Dual.eq_of_preReflection_mapsTo hfin hspan (P.coroot_root_two j) ?_ hg hgmaps
  rintro _ ⟨m, rfl⟩
  refine ⟨P.reflectionPerm j m, ?_⟩
  rw [P.root_reflectionPerm, P.reflection_apply, Module.preReflection_apply]

variable [IsAlgClosed k]

/-- **Almost simplicity from an irreducible root system.** Let `G` be semisimple over an
algebraically closed field with a split maximal torus `t`. If some root pairing on the rational
root span, whose roots are exactly the actual roots of `t`, is irreducible, then `G` is almost
simple. -/
theorem isAlmostSimple_of_isIrreducible (hG : IsSemisimple G) (t : T.toGrp ⟶ G)
    (hsplit : IsSplitSubtorus t) (hmax : IsMaximalTorus t)
    {J W : Type*} [AddCommGroup W] [Module ℚ W]
    (P : RootPairing J ℚ (relativeRootSpan t) W)
    (hP : Subtype.val '' Set.range P.root = toRat '' relativeRoots t)
    (hirr : P.IsIrreducible) : IsAlmostSimple G := by
  classical
  have hT : IsSplitTorus T.toGrp := hsplit.1
  have hCR : IsConnectedReductive G := hG.isConnectedReductive
  let : Smooth G.X.hom := hCR.smooth
  let : Mono t.hom.hom.left := hmax.2.1.mono
  obtain ⟨J', _, PZ, hPZ, -⟩ := rootDatumExistence k G hCR T hT t hmax
  have hrootZ (r : J') : PZ.root r ∈ relativeRoots t := by
    rw [relativeRoots_eq_roots, ← hPZ.2.1]
    exact Set.mem_range_self r
  -- The actual root of every index of `P`.
  have hidx : ∀ j : J, ∃ r : J', toRat (PZ.root r) = (P.root j).val := by
    intro j
    have hmem : (P.root j).val ∈ toRat '' relativeRoots t := hP ▸ ⟨P.root j, ⟨j, rfl⟩, rfl⟩
    obtain ⟨α, hα, hαj⟩ := hmem
    obtain ⟨r, hr⟩ : α ∈ Set.range PZ.root := by rw [hPZ.2.1]; exact hα
    exact ⟨r, hr ▸ hαj⟩
  choose F hF using hidx
  have hjr : ∀ r : J', ∃ j : J, F j = r := by
    intro r
    obtain ⟨j, hj⟩ := exists_root_eq_rationalRoot t P hP (hrootZ r)
    refine ⟨j, PZ.root.injective (hT.character_toRat_injective ?_)⟩
    rw [hF j, hj]
  -- Rational pairings are the integral pairings.
  have hratpair : ∀ i j : J, P.pairing i j = (PZ.pairing (F i) (F j) : ℚ) := by
    intro i j
    rw [← P.root_coroot'_eq_pairing,
      coroot'_eq_corootFunctional hT hPZ P hP j (F j) (hF j)]
    have hi : P.root i = RelativeRootSystem.rootVector t (hPZ.relativeRootEquiv (F i)) :=
      Subtype.ext (hF i).symm
    rw [hi, RelativeRootSystem.corootFunctional_rootVector, hPZ.relativeRootEquiv_val,
      ← hPZ.1, PZ.root_coroot_eq_pairing]
  -- Irreducibility gives a root.
  have := hirr
  have : Nontrivial (relativeRootSpan t) := RootPairing.IsIrreducible.nontrivial P
  obtain ⟨x, hx⟩ := exists_ne (0 : relativeRootSpan t)
  have hxmem : x ∈ P.rootSpan ℚ := by
    rw [rootSpan_eq_top_of_full_relativeRoot_image t P hP]
    exact Submodule.mem_top
  obtain ⟨j₀⟩ : Nonempty J := by
    by_contra hJ
    rw [not_nonempty_iff] at hJ
    apply hx
    have hbot : P.rootSpan ℚ = ⊥ := by
      rw [RootPairing.rootSpan, Set.range_eq_empty, Submodule.span_empty]
    rw [hbot] at hxmem
    exact (Submodule.mem_bot ℚ).mp hxmem
  refine ⟨hG, ?_, ?_⟩
  · -- Noncommutativity: `U_β` and `U_{-β}` do not commute.
    intro hc
    have h0 := RootPairNoncommutation.pairing_eq_zero_of_commute hCR hT hmax hPZ
      (F j₀) (F j₀) (fun Z x _ y _ => hc Z x y)
    rw [RootPairing.pairing_same] at h0
    norm_num at h0
  · intro H h hh hs hc hn
    let : Smooth H.X.hom := hs
    let : ConnectedSpace H.X.left := hc
    let : IsAffineHom H.X.hom := hh.isAffineHom
    let : IsClosedImmersion h.hom.hom.left := hh
    let : Mono h.hom.hom := Over.mono_of_mono_left _
    have hdich := semisimpleNormalRootDichotomy k G hG T t hsplit hmax H h hh hn
    let A : Set J' := {r | RelativeRoot.subgroup t (PZ.root r) ≤ SubgroupFunctor.range h}
    have hfix : ∀ r, r ∉ A → RelativeRoot.subgroup t (PZ.root r) ≤
        (AutomorphicAction.conjugation h).fixedSubgroup :=
      fun r hr => (hdich _ (hrootZ r)).resolve_left hr
    have hcommHF : ∀ (Z : Over (Spec (CommRingCat.of k))) (x y : Z ⟶ G.X),
        x ∈ (SubgroupFunctor.range h).carrier Z →
        y ∈ (AutomorphicAction.conjugation h).fixedSubgroup.carrier Z → Commute x y := by
      intro Z x y hx hy
      obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.1 hx
      have hc := (mem_conjugation_fixedSubgroup_iff h y).mp hy Z (𝟙 Z) z
      rw [Category.id_comp] at hc
      exact hc
    -- The roots outside `A` are stable under negation.
    have hnegA : ∀ r s : J', r ∉ A → PZ.root s = -PZ.root r → s ∉ A := by
      intro r s hr hs hsA
      have hsA' : RelativeRoot.subgroup t (PZ.root s) ≤ SubgroupFunctor.range h := hsA
      have h0 := RootPairNoncommutation.pairing_eq_zero_of_commute hCR hT hmax hPZ s r
        (fun Z x hx y hy => by
          rcases hy with hy | hy
          · exact hcommHF Z x y (hsA' Z hx) (hfix r hr Z hy)
          · rw [← hs] at hy
            exact RootPairNoncommutation.commute_of_mem_same_root hCR hT hmax hPZ s hx hy)
      have hpair : PZ.pairing s r = -2 := by
        rw [← PZ.root_coroot_eq_pairing, hs, map_neg, LinearMap.neg_apply,
          PZ.root_coroot_eq_pairing, RootPairing.pairing_same]
      rw [hpair] at h0
      norm_num at h0
    -- Roots inside and outside `A` are orthogonal.
    have horth : ∀ a b : J', a ∈ A → b ∉ A → PZ.pairing a b = 0 := by
      intro a b ha hb
      have ha' : RelativeRoot.subgroup t (PZ.root a) ≤ SubgroupFunctor.range h := ha
      obtain ⟨b', hb'⟩ : -PZ.root b ∈ Set.range PZ.root :=
        PZ.neg_mem_range_root_iff.mpr (Set.mem_range_self b)
      have hb'A : b' ∉ A := hnegA b b' hb hb'
      refine RootPairNoncommutation.pairing_eq_zero_of_commute hCR hT hmax hPZ a b
        (fun Z x hx y hy => ?_)
      rcases hy with hy | hy
      · exact hcommHF Z x y (ha' Z hx) (hfix b hb Z hy)
      · rw [← hb'] at hy
        exact hcommHF Z x y (ha' Z hx) (hfix b' hb'A Z hy)
    by_cases hex : ∃ r, r ∈ A
    · right
      obtain ⟨r₀, hr₀⟩ := hex
      obtain ⟨i₀, hi₀⟩ := hjr r₀
      let s : Set J := {j | F j ∈ A}
      have hs_ne : s.Nonempty := ⟨i₀, show F i₀ ∈ A by rw [hi₀]; exact hr₀⟩
      have horthJ : ∀ i ∈ s, ∀ j ∉ s, P.pairing i j = 0 := by
        intro i hi j hj
        rw [hratpair, horth (F i) (F j) hi hj, Int.cast_zero]
      have hspan := P.span_root_image_eq_top_of_forall_orthogonal s hs_ne
        (fun j hj i hi => by
          have hjs : j ∉ s := fun hjs => hj (Submodule.subset_span ⟨j, hjs, rfl⟩)
          have h1 := horthJ i hi j hjs
          exact ⟨P.pairing_eq_zero_iff'.mp h1, h1⟩)
      have hall : ∀ j : J, j ∈ s := by
        intro j
        by_contra hj
        have hker : Submodule.span ℚ (P.root '' s) ≤ LinearMap.ker (P.coroot' j) := by
          rw [Submodule.span_le]
          rintro _ ⟨i, hi, rfl⟩
          rw [SetLike.mem_coe, LinearMap.mem_ker, P.root_coroot'_eq_pairing]
          exact horthJ i hi j hj
        rw [hspan] at hker
        have h2 := hker (Submodule.mem_top : P.root j ∈ ⊤)
        rw [LinearMap.mem_ker, P.coroot_root_two] at h2
        norm_num at h2
      exact semisimpleRootGeneration k G hG T t hsplit hmax H h hh fun β hβ => by
        obtain ⟨r, rfl⟩ : β ∈ Set.range PZ.root := by rw [hPZ.2.1]; exact hβ
        obtain ⟨j, rfl⟩ := hjr r
        exact hall j
    · left
      have hfixed : ∀ β ∈ relativeRoots t,
          RelativeRoot.subgroup t β ≤ (AutomorphicAction.conjugation h).fixedSubgroup := by
        intro β hβ
        obtain ⟨r, rfl⟩ : β ∈ Set.range PZ.root := by rw [hPZ.2.1]; exact hβ
        exact hfix r fun hr => hex ⟨r, hr⟩
      have hcentral : (AutomorphicAction.conjugation h).fixedSubgroup = ⊤ :=
        (AutomorphicAction.conjugation h).fixedSubgroup_eq_top_of_rootGeneration
          semisimpleRootGeneration hG T t hsplit hmax inferInstance hfixed
      have hH : IsSemisimple H := hG.of_normalSubgroup h hh hn
      have hcomm : ∀ (W : Over (Spec (CommRingCat.of k))) (x y : W ⟶ H.X), Commute x y := by
        intro W x y
        apply (commute_iff_eq _ _).mpr
        apply (cancel_mono h.hom.hom).mp
        have hm : y ≫ h.hom.hom ∈
            (AutomorphicAction.conjugation h).fixedSubgroup.carrier W := by
          rw [hcentral]
          trivial
        have he := (mem_conjugation_fixedSubgroup_iff h _).mp hm W (𝟙 W) x
        simpa only [Category.id_comp, MonObj.mul_comp] using he.eq
      have hzH : SubgroupFunctor.range (𝟙 H) = ⊥ := by
        by_contra hnt'
        exact hH.noncommutative_of_range_ne_bot hnt' hcomm
      simpa only [Category.id_comp] using
        (SubgroupFunctor.range_comp_eq_bot_iff (𝟙 H) h).mpr hzH

end Irreducible

/-- **Conrad, *Reductive group schemes*, Corollary 5.1.18.** A nontrivial semisimple group over
a field is absolutely almost simple if and only if the root system of its base change to the
algebraic closure, with respect to a maximal torus, is irreducible. -/
theorem absolutelyAlmostSimpleIrreducible :
    AbsolutelyAlmostSimpleIrreducibleStatement.{u} := by
  intro k _ G hG _ T i hi
  have := hG.isConnectedReductive.isAffineHom
  have : IsAffineHom ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (toAlgebraicClosure k)))
  intro J P heval hroots
  have hG' : IsSemisimple ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G) :=
    hG.baseChange_toAlgebraicClosure
  have hmax : IsMaximalTorus i :=
    hi.isMaximalTorus (toriAreSplit_of_isSepClosed (AlgebraicClosure k))
  constructor
  · intro habs
    exact relativeRootSystemIrreducible (AlgebraicClosure k) _ habs.2 T i hi
      (habs.2.relativeRoots_nonempty_of_split_maximalTorus i hi.1.1 hmax) J P heval hroots
  · intro hirr
    have h' := isAlmostSimple_of_isIrreducible hG' i hi.1 hmax P hroots hirr
    exact ⟨IsAlmostSimple.of_fieldExtension (K := AlgebraicClosure k) h', h'⟩

end Langlands.GroupScheme
