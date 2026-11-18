import Langlands.GroupScheme.Rational.NormalSubgroupIntersectionStatement
import Langlands.GroupScheme.Absolute.MaximalRankRadicalTorusIntersectionOfComplement
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Absolute.SolvableMaximalTorusSemidirectProof
import Langlands.GroupScheme.Cartan.StructureProof
import Langlands.GroupScheme.Cartan.Basic
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.CommutativeSubgroupIntersectionComparison
import Langlands.GroupScheme.ReducedSubgroup
import Langlands.GroupScheme.NormalizerRepresentability
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Maximal tori meet normalized smooth connected subgroups in maximal tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace NormalSubgroupIntersection

variable {k : Type u} [Field k]

/-- Inside a smooth connected affine group over an algebraically closed field, let
`f : T → H` be a maximal torus and `r : N → H` a smooth connected closed subgroup with normal
range. Then a maximal torus of `N` factors through `f` by a closed map, and its image is the
whole intersection of the ranges of `f` and `r` on every test scheme. -/
theorem exists_torusIntersection_of_isNormal [IsAlgClosed k]
    {H N : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (f : T.toGrp ⟶ H)
    (hf : IsMaximalTorus f) (r : N ⟶ H) (hr : IsClosedSubgroup r)
    (hNs : Smooth N.X.hom) (hNc : ConnectedSpace N.X.left)
    (hn : (SubgroupFunctor.range r).IsNormal) :
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of k)))
      (sT : S.toGrp ⟶ T.toGrp) (sR : S.toGrp ⟶ N),
      IsClosedSubgroup sT ∧ IsMaximalTorus sR ∧
      sT ≫ f = sR ≫ r ∧
      SubgroupFunctor.range (sT ≫ f) =
        SubgroupFunctor.range f ⊓ SubgroupFunctor.range r := by
  have : IsAffineHom N.X.hom := hr.isAffineHom
  have : LocallyOfFiniteType N.X.hom := hr.locallyOfFiniteType
  have : IsAffine N.X.left := isAffine_of_isAffineHom N.X.hom
  have hT : IsSplitTorus T.toGrp :=
    IsTorus.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting hf.1
  -- A maximal torus of `N`, enlarged to a maximal torus of `H`, conjugated onto `f`.
  obtain ⟨S₀, s₀, hs₀⟩ := exists_isMaximalTorus N
  obtain ⟨T₁, t₁, ht₁, a, ha⟩ :=
    exists_maximalTorus_extension_of_finiteType H (s₀ ≫ r) hs₀.1 (hs₀.2.1.comp hr)
  obtain ⟨g, e, hg⟩ := maximalTorusConjugacy.maximalToriAreConjugate k H T₁ T t₁ f ht₁ hf
  have hrep := hr.isRepresentedBy_range
  let c := hrep.conjugateIso hn g
  let sR : S₀.toGrp ⟶ N := s₀ ≫ c.hom
  let sT : S₀.toGrp ⟶ T.toGrp := a ≫ e.hom
  have hsR : IsMaximalTorus sR := hs₀.comp_iso c
  have hsq : sT ≫ f = sR ≫ r := by
    simp only [sT, sR, c, Category.assoc,
      SubgroupFunctor.IsRepresentedBy.conjugateIso_hom_comp]
    rw [← hg, ← Category.assoc a t₁, ha, Category.assoc]
  have hsT : IsClosedSubgroup sT :=
    IsClosedSubgroup.of_comp hf.2.1 (hsq ▸ hsR.2.1.comp hr)
  refine ⟨S₀, sT, sR, hsT, hsR, hsq, ?_⟩
  -- The Cartan subgroup of `N` attached to `sR` and its unipotent-by-torus decomposition.
  obtain ⟨C, cN, hC, hCrep⟩ := exists_isCartanSubgroup_of_isMaximalTorus hsR
  obtain ⟨hCs, hCc, hCnil⟩ := cartanStructure k N C cN hC
  have : Smooth C.X.hom := hCs
  have : ConnectedSpace C.X.left := hCc
  have : IsAffineHom C.X.hom := hC.1.isAffineHom
  have : Mono sR.hom.hom := by
    have : IsClosedImmersion sR.hom.hom.left := hsR.2.1
    exact Over.mono_of_mono_left _
  have : Mono cN.hom.hom := hCrep.1
  have hle : SubgroupFunctor.range sR ≤ SubgroupFunctor.range cN := by
    rw [hCrep.2]
    exact range_le_torusCentralizer sR
  obtain ⟨sC, hsC⟩ := SubgroupFunctor.exists_factor_of_range_le hle
  have hsCmax : IsMaximalTorus sC := IsMaximalTorus.of_comp hC.1 (hsC.symm ▸ hsR)
  obtain ⟨U, u, hu, -, -, hU, -, -, hmul⟩ :=
    solvableMaximalTorusSemidirect k C hCnil.isSolvableGroupScheme S₀ sC hsCmax
  have : IsAffineHom U.X.hom := hu.isAffineHom
  have : LocallyOfFiniteType U.X.hom := hu.locallyOfFiniteType
  let v : U ⟶ H := u ≫ cN ≫ r
  -- The torus `T` meets the unipotent part `U` trivially.
  have hbot : ∀ (V : Over (Spec (CommRingCat.of k))) (p : V ⟶ H.X),
      p ∈ (SubgroupFunctor.range f).carrier V →
        p ∈ (SubgroupFunctor.range v).carrier V → p = 1 := by
    intro V p hpf hpu
    have hsnd : IsClosedSubgroup (subgroupIntersectionSnd f v) := by
      have : IsClosedImmersion f.hom.hom.left := hf.2.1
      have : IsClosedImmersion (subgroupIntersectionSnd f v).hom.hom.left :=
        MorphismProperty.of_isPullback (subgroupIntersection_isPullback_scheme f v) this
      exact this
    have hW : IsUnipotent (subgroupIntersection f v) :=
      unipotentClosedSubgroup k U (subgroupIntersection f v) _ hsnd hU
    have hp : p ∈ (SubgroupFunctor.range (subgroupIntersectionHom f v)).carrier V := by
      rw [range_subgroupIntersectionHom]
      exact ⟨hpf, hpu⟩
    obtain ⟨q, rfl⟩ := SubgroupFunctor.mem_range.1 hp
    change q ≫ (subgroupIntersectionFst f v).hom.hom ≫ f.hom.hom = 1
    rw [← Category.assoc,
      hW.comp_eq_one_of_isSplitTorus hT (subgroupIntersectionFst f v) V q,
      MonObj.one_comp]
  apply le_antisymm
  · intro V x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    refine ⟨⟨y ≫ sT.hom.hom, ?_⟩, ⟨y ≫ sR.hom.hom, ?_⟩⟩
    · change (y ≫ sT.hom.hom) ≫ f.hom.hom = y ≫ (sT ≫ f).hom.hom
      simp only [Grp.comp_hom_hom, Category.assoc]
    · change (y ≫ sR.hom.hom) ≫ r.hom.hom = y ≫ (sT ≫ f).hom.hom
      rw [hsq]
      simp only [Grp.comp_hom_hom, Category.assoc]
  · rintro V x ⟨hxf, hxr⟩
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hxf
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1 hxr
    -- The point `z` of `N` centralizes the maximal torus `sR`.
    have hzC : z ∈ (torusCentralizer sR).carrier V := by
      intro W a t'
      have : Mono r.hom.hom := hrep.1
      apply (commute_iff_eq _ _).mpr
      apply (cancel_mono r.hom.hom).1
      have h1 : (a ≫ z) ≫ r.hom.hom = (a ≫ y) ≫ f.hom.hom := by
        rw [Category.assoc, Category.assoc, hz, hy]
      have h2 : (t' ≫ sR.hom.hom) ≫ r.hom.hom = (t' ≫ sT.hom.hom) ≫ f.hom.hom := by
        have := congrArg (fun φ : S₀.toGrp ⟶ H => φ.hom.hom) hsq
        simp only [Grp.comp_hom_hom] at this
        rw [Category.assoc, Category.assoc, this]
      rw [MonObj.mul_comp, MonObj.mul_comp, h1, h2, ← MonObj.mul_comp, ← MonObj.mul_comp,
        mul_comm]
    rw [← hCrep.2] at hzC
    obtain ⟨z', hz'⟩ := SubgroupFunctor.mem_range.1 hzC
    let m := subgroupMultiplication u sC
    let w : V ⟶ U.X ⊗ S₀.toGrp.X := z' ≫ inv m
    have hzw : z' = (w ≫ fst _ _ ≫ u.hom.hom) * (w ≫ snd _ _ ≫ sC.hom.hom) := by
      rw [← Category.assoc, ← Category.assoc, ← comp_subgroupMultiplication,
        lift_comp_fst_snd]
      simp only [w, m, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hx : x = ((w ≫ fst _ _) ≫ v.hom.hom) *
        ((w ≫ snd _ _) ≫ (sT ≫ f).hom.hom) := by
      rw [← hz, ← hz', hzw, MonObj.mul_comp, MonObj.mul_comp, hsq, ← hsC]
      simp only [v, Grp.comp_hom_hom, Category.assoc]
    have hft : (w ≫ snd _ _) ≫ (sT ≫ f).hom.hom ∈ (SubgroupFunctor.range f).carrier V :=
      SubgroupFunctor.mem_range.2
        ⟨(w ≫ snd _ _) ≫ sT.hom.hom, by simp only [Grp.comp_hom_hom, Category.assoc]⟩
    have hn1 : (w ≫ fst _ _) ≫ v.hom.hom = 1 := by
      apply hbot V
      · have hq : (w ≫ fst _ _) ≫ v.hom.hom =
            x * ((w ≫ snd _ _) ≫ (sT ≫ f).hom.hom)⁻¹ := by
          rw [hx, mul_inv_cancel_right]
        rw [hq]
        exact Subgroup.mul_mem _ hxf (Subgroup.inv_mem _ hft)
      · exact SubgroupFunctor.mem_range.2 ⟨w ≫ fst _ _, rfl⟩
    rw [hx, hn1, one_mul]
    exact SubgroupFunctor.mem_range.2 ⟨w ≫ snd _ _, rfl⟩

/-- Over an algebraically closed field, let `t : T → G` be a maximal torus of an affine group
locally of finite type and `n : N → G` a smooth connected closed subgroup normalized by `T`.
Then a maximal torus of `N` factors through `t` by a closed map, and its image is the whole
intersection of the ranges of `t` and `n` on every test scheme. -/
theorem exists_torusIntersection_of_isNormalizedBy [IsAlgClosed k]
    {G N : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (t : T.toGrp ⟶ G)
    (ht : IsMaximalTorus t) (n : N ⟶ G) (hn : IsClosedSubgroup n)
    (hNs : Smooth N.X.hom) (hNc : ConnectedSpace N.X.left)
    (hnorm : (SubgroupFunctor.range n).IsNormalizedBy (SubgroupFunctor.range t)) :
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of k)))
      (sT : S.toGrp ⟶ T.toGrp) (sR : S.toGrp ⟶ N),
      IsClosedSubgroup sT ∧ IsMaximalTorus sR ∧
      sT ≫ t = sR ≫ n ∧
      SubgroupFunctor.range (sT ≫ t) =
        SubgroupFunctor.range t ⊓ SubgroupFunctor.range n := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  -- The normalizer `M` of `N` and the reduced identity component `H` of `M`.
  obtain ⟨M, m, hm, hmrep⟩ := (hasClosedRepresentative_normalizer_centralizer_range n hn).1
  obtain ⟨H, f, hι, hHs, hHc, -, hfac⟩ := ReducedSubgroup.exists_reducedIdentityComponent m hm
  have : Smooth H.X.hom := hHs
  have : ConnectedSpace H.X.left := hHc
  have : IsAffineHom H.X.hom := hι.isAffineHom
  have : Mono (f ≫ m).hom.hom := by
    have : IsClosedImmersion (f ≫ m).hom.hom.left := hι
    exact Over.mono_of_mono_left _
  have : Mono n.hom.hom := hn.isRepresentedBy_range.1
  -- The torus `T` normalizes `N`.
  have hTle : SubgroupFunctor.range t ≤ SubgroupFunctor.range m := by
    rw [hmrep.2]
    intro U g hg V a x hx
    have hag : a ≫ g ∈ (SubgroupFunctor.range t).carrier V :=
      (SubgroupFunctor.range t).comp_mem a hg
    refine ⟨hnorm V _ x hag hx, ?_⟩
    simpa only [inv_inv] using hnorm V _ x (Subgroup.inv_mem _ hag) hx
  have hNle : SubgroupFunctor.range n ≤ SubgroupFunctor.range m := by
    rw [hmrep.2]
    exact SubgroupFunctor.le_normalizer _
  obtain ⟨eT, heT⟩ := hfac T.toGrp t ht.2.1 ht.1.smooth ht.1.connectedSpace hTle
  obtain ⟨eN, heN⟩ := hfac N n hn hNs hNc hNle
  have heT' : eT ≫ (f ≫ m) = t := heT
  have heN' : eN ≫ (f ≫ m) = n := heN
  have hTmax : IsMaximalTorus eT := IsMaximalTorus.of_comp hι (heT'.symm ▸ ht)
  have hNcl : IsClosedSubgroup eN := IsClosedSubgroup.of_comp hι (heN'.symm ▸ hn)
  -- `N` is normal in `H`, since `H` lies in the normalizer of `N`.
  have hNnormal : (SubgroupFunctor.range eN).IsNormal := by
    intro V g x _ hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    have hg : g ≫ (f ≫ m).hom.hom ∈ (SubgroupFunctor.range m).carrier V :=
      SubgroupFunctor.mem_range.2 ⟨g ≫ f.hom.hom, by
        simp only [Grp.comp_hom_hom, Category.assoc]⟩
    rw [hmrep.2] at hg
    have hy : (y ≫ eN.hom.hom) ≫ (f ≫ m).hom.hom ∈ (SubgroupFunctor.range n).carrier V :=
      SubgroupFunctor.mem_range.2 ⟨y, by
        rw [Category.assoc, ← Grp.comp_hom_hom, heN']⟩
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1
      (SubgroupFunctor.conj_mem_of_mem_normalizer hg hy)
    refine SubgroupFunctor.mem_range.2 ⟨z, ?_⟩
    apply (cancel_mono (f ≫ m).hom.hom).1
    rw [Category.assoc, ← Grp.comp_hom_hom, heN', hz, MonObj.mul_comp, MonObj.mul_comp,
      GrpObj.inv_comp]
  obtain ⟨S, sT, sR, hsT, hsR, hsq, hrange⟩ :=
    exists_torusIntersection_of_isNormal eT hTmax eN hNcl hNs hNc hNnormal
  have hsq' : sT ≫ t = sR ≫ n := by
    rw [← heT', ← heN', ← Category.assoc, hsq, Category.assoc]
  refine ⟨S, sT, sR, hsT, hsR, hsq', ?_⟩
  apply le_antisymm
  · intro V x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    refine ⟨⟨y ≫ sT.hom.hom, ?_⟩, ⟨y ≫ sR.hom.hom, ?_⟩⟩
    · change (y ≫ sT.hom.hom) ≫ t.hom.hom = y ≫ (sT ≫ t).hom.hom
      simp only [Grp.comp_hom_hom, Category.assoc]
    · change (y ≫ sR.hom.hom) ≫ n.hom.hom = y ≫ (sT ≫ t).hom.hom
      rw [hsq']
      simp only [Grp.comp_hom_hom, Category.assoc]
  · rintro V x ⟨hxt, hxn⟩
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hxt
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1 hxn
    have hyz : y ≫ eT.hom.hom = z ≫ eN.hom.hom := by
      apply (cancel_mono (f ≫ m).hom.hom).1
      rw [Category.assoc, Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, heT',
        heN', hz]
    have hmem : y ≫ eT.hom.hom ∈
        (SubgroupFunctor.range eT ⊓ SubgroupFunctor.range eN).carrier V :=
      ⟨⟨y, rfl⟩, ⟨z, hyz.symm⟩⟩
    rw [← hrange] at hmem
    obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.1 hmem
    refine SubgroupFunctor.mem_range.2 ⟨w, ?_⟩
    rw [← heT']
    simp only [Grp.comp_hom_hom, ← Category.assoc] at hw ⊢
    rw [hw]

/-- Conrad, *Reductive group schemes*, Exercise 5.5.1(i), over an arbitrary field: for a
maximal torus `t : T → G` of a smooth affine group and a smooth connected closed subgroup
`n : N → G` normalized by `T`, the scheme-theoretic intersection of `T` and `N` is a maximal
torus of `N` representing `range n ⊓ range t`. -/
theorem torusIntersection (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G)
    (ht : IsMaximalTorus t) (N : GroupScheme (Spec (CommRingCat.of k))) (n : N ⟶ G)
    (hn : IsClosedSubgroup n) (hNs : Smooth N.X.hom) (hNc : ConnectedSpace N.X.left)
    (hnorm : (SubgroupFunctor.range n).IsNormalizedBy (SubgroupFunctor.range t)) :
    ∃ (C : CommGroupScheme (Spec (CommRingCat.of k))) (c : C.toGrp ⟶ N),
      IsMaximalTorus c ∧
        SubgroupFunctor.range (c ≫ n) =
          SubgroupFunctor.range n ⊓ SubgroupFunctor.range t := by
  let K := AlgebraicClosure k
  let b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : Mono n.hom.hom := hn.isRepresentedBy_range.1
  have : IsAffineHom N.X.hom := hn.isAffineHom
  have : Smooth N.X.hom := hNs
  have : ConnectedSpace N.X.left := hNc
  have : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom b)
    infer_instance
  have hNKs : Smooth ((GroupScheme.baseChange b).obj N).X.hom := by
    change Smooth (pullback.snd N.X.hom b)
    infer_instance
  have hNKc : ConnectedSpace ((GroupScheme.baseChange b).obj N).X.left :=
    connectedSpace_baseChange_of_smooth_affine N b
  have htK := (maximalTorusBaseChange k K G T t ht.1 ht.2.1).1 ht
  have hnormK : (SubgroupFunctor.range ((GroupScheme.baseChange b).map n)).IsNormalizedBy
      (SubgroupFunctor.range ((GroupScheme.baseChange b).map t)) := by
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom]
    exact hnorm.baseChange b
  obtain ⟨S, sT, sR, hsT, hsR, hsq, hrange⟩ :=
    exists_torusIntersection_of_isNormalizedBy
      (T := (CommGroupScheme.baseChange b).obj T) ((GroupScheme.baseChange b).map t) htK
      ((GroupScheme.baseChange b).map n) (hn.baseChange b) hNKs hNKc hnormK
  have hc := isMaximalTorus_commutativeSubgroupIntersectionSnd_of_baseChange_representative
    (K := K) t n sT sR ht.2.1 hn hsT hsR hsq hrange
  refine ⟨commutativeSubgroupIntersection t n, commutativeSubgroupIntersectionSnd t n, hc, ?_⟩
  rw [← commutativeSubgroupIntersection_condition, range_commutativeSubgroupIntersection]
  exact SubgroupFunctor.ext fun V => by
    rw [SubgroupFunctor.inf_carrier, SubgroupFunctor.inf_carrier, inf_comm]

end NormalSubgroupIntersection

end Langlands.GroupScheme
