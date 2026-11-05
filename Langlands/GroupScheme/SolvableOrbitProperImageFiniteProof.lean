import Langlands.GroupScheme.StabilizerImageDichotomy
import Langlands.GroupScheme.HomogeneousProperImageFibre
import Langlands.GroupScheme.StabilizerClosedSubgroup
import Langlands.GroupScheme.OrbitMapFlatProof
import Langlands.GroupScheme.SchemeActionOrbitDescent
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.AlgebraicallyClosedSplitSolvableProof
import Langlands.GroupScheme.SolvableOrbitProperImageFiniteStatement
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker

/-! # Finite proper images in homogeneous spaces of split-solvable groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SolvableOrbitProperImage

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- One induction step: a group with a normal subgroup `N` and an elementary fppf
quotient `V` has one-point proper images once `N` has them. -/
theorem hasOnePointProperImages_succ
    {G N V : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [Smooth N.X.hom]
    (jN : N ⟶ G) (q : G ⟶ V)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range jN) q)
    (hV : SplitSolvable.IsElementaryQuotient V) (hN : HasOnePointProperImages N) :
    HasOnePointProperImages G := by
  intro O hred hsep hlft hqc a x htrans Z hZ hZred hZconn j
  -- The stabilizer of `x` and its image in `V`.
  have hu : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ := toUnit_unique _ _
  obtain ⟨K, iK, hiK, hK⟩ := a.exists_isClosedSubgroup_stabilizer x
  have hKw : iK.hom.hom.left ≫ G.X.hom = K.X.hom := Over.w iK.hom.hom
  have : IsClosedImmersion iK.hom.hom.left := hiK
  have : IsAffineHom K.X.hom := hKw ▸ inferInstance
  have : LocallyOfFiniteType K.X.hom := hKw ▸ inferInstance
  -- Rational points of the stabilizer fix `x`.
  have hfix : ∀ s : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ K.X,
      a.act (s ≫ iK.hom.hom) x = x := by
    intro s
    have h := (hK _ (s ≫ iK.hom.hom)).mp (SubgroupFunctor.mem_range.mpr ⟨s, rfl⟩)
    simpa only [hu, Category.id_comp] using h
  have hfixinv : ∀ s : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ K.X,
      a.act (s ≫ iK.hom.hom)⁻¹ x = x := by
    intro s
    conv_lhs => rw [← hfix s]
    rw [← a.act_mul, inv_mul_cancel, a.act_one]
  -- Points of `N` are killed by `q`.
  have hker : ∀ {T : Over (Spec (CommRingCat.of k))} (n : T ⟶ N.X),
      (n ≫ jN.hom.hom) ≫ q.hom.hom = 1 := by
    intro T n
    have hn : n ≫ jN.hom.hom ∈ (SubgroupFunctor.range jN).carrier T :=
      SubgroupFunctor.mem_range.mpr ⟨n, rfl⟩
    rw [← hq.2.2.2] at hn
    exact (mem_range_kernelι_iff q _).mp hn
  -- Equal images in `V` give a point of `N`.
  have hlift : ∀ g h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      g ≫ q.hom.hom = h ≫ q.hom.hom →
        ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ N.X, n ≫ jN.hom.hom = g * h⁻¹ := by
    intro g h e
    have hm := SchemeAction.inv_mul_mem_range_of_fppf_quotient jN q hq g⁻¹ h⁻¹
      (by rw [GrpObj.inv_comp, GrpObj.inv_comp, e])
    rw [inv_inv] at hm
    exact SubgroupFunctor.mem_range.mp hm
  rcases stabilizerImageDichotomy k K V (iK ≫ q) hV with hA | ⟨W, χ, hW, hinv, hsepχ⟩
  · -- Case A: `N(k)` is already transitive on `O(k)`.
    refine hN O hred hsep hlft hqc (a.restrict jN) x ?_ Z hZ hZred hZconn j
    intro y
    obtain ⟨g, rfl⟩ := htrans y
    obtain ⟨s, hs⟩ := hA (g ≫ q.hom.hom)
    obtain ⟨n, hn⟩ := hlift g (s ≫ iK.hom.hom) (by
      rw [← hs, Grp.comp_hom_hom, Category.assoc])
    refine ⟨n, ?_⟩
    rw [SchemeAction.restrict_act, hn, a.act_mul, hfixinv]
  · -- Case B: descend the invariant function along the orbit map.
    have : IsAffine W.left := hW
    have : IsReduced O.left := hred
    have : LocallyOfFiniteType O.hom := hlft
    obtain ⟨hfl, hsu, hqc'⟩ := orbitMapFaithfullyFlat k G O a x htrans
    have : Flat (a.orbitMap x).left := hfl
    have : Surjective (a.orbitMap x).left := hsu
    have : QuasiCompact (a.orbitMap x).left := hqc'
    obtain ⟨f, hf⟩ := FiniteIndexTransfer.exists_factor iK (q.hom.hom ≫ χ) (a.orbitMap x)
      (fun T g h he => by
        rw [hK]
        rw [SchemeAction.comp_orbitMap, SchemeAction.comp_orbitMap] at he
        rw [a.act_mul, ← he, ← a.act_mul, inv_mul_cancel, a.act_one])
      (fun T g h hgh => by
        obtain ⟨s, hs⟩ := SubgroupFunctor.mem_range.mp hgh
        have hh : h = g * (s ≫ iK.hom.hom) := by rw [hs, mul_inv_cancel_left]
        rw [hh, ← Category.assoc, ← Category.assoc, MonObj.mul_comp, Category.assoc s,
          ← Grp.comp_hom_hom]
        exact (hinv T (g ≫ q.hom.hom) s).symm)
    have e : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        a.act g x ≫ f = (g ≫ q.hom.hom) ≫ χ := by
      intro g
      have h := a.comp_orbitMap x g
      rw [hu, Category.id_comp] at h
      rw [← h, Category.assoc, hf, Category.assoc]
    have : IsSeparated O.hom := hsep
    have : QuasiCompact O.hom := hqc
    have : IsProper Z.hom := hZ
    have : IsReduced Z.left := hZred
    have : ConnectedSpace Z.left := hZconn
    refine hN.subsingleton_range_of_fibres (a.restrict jN) f ?_ ?_ j
    · intro n y
      obtain ⟨g, rfl⟩ := htrans y
      rw [SchemeAction.restrict_act, ← a.act_mul, e, e, MonObj.mul_comp, hker, one_mul]
    · intro y z hyz
      obtain ⟨g₁, rfl⟩ := htrans y
      obtain ⟨g₂, rfl⟩ := htrans z
      rw [e, e] at hyz
      obtain ⟨s, hs⟩ := hsepχ _ _ hyz
      obtain ⟨n, hn⟩ := hlift g₂ (g₁ * (s ≫ iK.hom.hom)) (by
        rw [MonObj.mul_comp, ← hs, Category.assoc, Grp.comp_hom_hom])
      refine ⟨n, ?_⟩
      rw [SchemeAction.restrict_act, hn, ← a.act_mul, mul_inv_rev, mul_assoc,
        inv_mul_cancel_right, a.act_mul, hfixinv]

/-- Every smooth affine group with a Ga/Gm series has one-point proper images. -/
theorem hasOnePointProperImages_of_hasSeries (n : ℕ) :
    ∀ {G : GroupScheme (Spec (CommRingCat.of k))} [Smooth G.X.hom] [IsAffineHom G.X.hom],
      SplitSolvable.HasSeries n G → HasOnePointProperImages G := by
  induction n with
  | zero => intro G _ _ h; exact hasOnePointProperImages_of_range_id_eq_bot h
  | succ n ih =>
    intro G _ _ h
    obtain ⟨N, V, jN, q, hj, hs, -, -, hq, hV, hN⟩ := h
    have hNw : jN.hom.hom.left ≫ G.X.hom = N.X.hom := Over.w jN.hom.hom
    have : IsClosedImmersion jN.hom.hom.left := hj
    have : IsAffineHom N.X.hom := hNw ▸ inferInstance
    exact hasOnePointProperImages_succ jN q hq hV (ih hN)

end SolvableOrbitProperImage

/-- If `G` has one-point proper images, then every proper scheme has finite image in
each homogeneous space of `G` as in the target statement: each of the finitely many
irreducible components, with its reduced structure, has one-point image. -/
theorem HasOnePointProperImages.range_finite {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : HasOnePointProperImages G)
    (O : Over (Spec (CommRingCat.of k))) (hred : IsReduced O.left) (hsep : IsSeparated O.hom)
    (hlft : LocallyOfFiniteType O.hom) (hqc : QuasiCompact O.hom) (a : SchemeAction G O)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ O)
    (htrans : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ O,
      ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X, a.act g x = y)
    (Z : Over (Spec (CommRingCat.of k))) (hZ : IsProper Z.hom) (j : Z ⟶ O) :
    (Set.range j.left).Finite := by
  have : IsProper Z.hom := hZ
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : IsNoetherian Z.left := {}
  -- Each irreducible component has one-point image.
  have hcomp : ∀ C ∈ irreducibleComponents Z.left, (j.left '' C).Subsingleton := by
    intro C hC
    let I := Scheme.IdealSheafData.vanishingIdeal
      (⟨C, isClosed_of_mem_irreducibleComponents C hC⟩ : TopologicalSpace.Closeds Z.left)
    have hIred : IsReduced I.subscheme :=
      (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker _).1
    let Y : Over (Spec (CommRingCat.of k)) := Over.mk (I.subschemeι ≫ Z.hom)
    let i : Y ⟶ Z := Over.homMk I.subschemeι rfl
    have hrange : Set.range i.left = C := by
      change Set.range I.subschemeι = _
      rw [Scheme.IdealSheafData.range_subschemeι]
      rfl
    have : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion I.subschemeι)
    have hYp : IsProper Y.hom := by
      change IsProper (I.subschemeι ≫ Z.hom)
      infer_instance
    have hYc : ConnectedSpace Y.left := by
      have hCirr : IsIrreducible C := hC.1
      rw [connectedSpace_iff_univ]
      refine ⟨?_, ?_⟩
      · obtain ⟨c, hc⟩ := hCirr.nonempty
        rw [← hrange] at hc
        obtain ⟨y, -⟩ := hc
        exact ⟨y, Set.mem_univ y⟩
      · rw [← i.left.isClosedEmbedding.isInducing.isPreconnected_image, Set.image_univ,
          hrange]
        exact hCirr.isConnected.isPreconnected
    have h := hG O hred hsep hlft hqc a x htrans Y hYp hIred hYc (i ≫ j)
    rw [← hrange, ← Set.range_comp]
    simpa only [Over.comp_left, Scheme.Hom.comp_base, TopCat.hom_comp,
      ContinuousMap.coe_comp] using h
  refine (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.biUnion
    fun C hC => (hcomp C hC).finite).subset ?_
  rintro _ ⟨z, rfl⟩
  exact Set.mem_biUnion (irreducibleComponent_mem_irreducibleComponents z)
    ⟨z, mem_irreducibleComponent, rfl⟩

/-- The target statement, from the comparison theorem that smooth connected solvable
groups over an algebraically closed field are split. -/
theorem solvableOrbitProperImageFinite_of_split
    (hsplit : AlgebraicallyClosedSplitSolvableStatement.{u}) :
    SolvableOrbitProperImageFiniteStatement.{u} := by
  intro k _ _ G _ _ hconn hsolv O hred hsep hlft hqc a x htrans Z hZ j
  obtain ⟨n, hn⟩ := (hsplit k G hconn hsolv).hasSeries
  exact (SolvableOrbitProperImage.hasOnePointProperImages_of_hasSeries n hn
    ).range_finite O hred hsep hlft hqc a x htrans Z hZ j

/-- Proper schemes have finite images in homogeneous spaces of smooth connected
solvable affine groups over an algebraically closed field. -/
theorem solvableOrbitProperImageFinite : SolvableOrbitProperImageFiniteStatement.{u} :=
  solvableOrbitProperImageFinite_of_split algebraicallyClosedSplitSolvable

end Langlands.GroupScheme
