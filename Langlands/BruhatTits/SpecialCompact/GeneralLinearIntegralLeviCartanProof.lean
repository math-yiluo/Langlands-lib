import Langlands.BruhatTits.SpecialCompact.GeneralLinearIntegralLeviCartanStatement
import Langlands.BruhatTits.SpecialCompact.GeneralLinearIntegralCartanProof
import Langlands.BruhatTits.SpecialCompact.GeneralLinearStandardLeviIntegralPointsProof
import Langlands.GroupScheme.Rational.ParabolicFunctor
import Langlands.GroupScheme.Rational.StandardLeviStandardFamiliesProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Dynamic.LieProof

/-! # Block Cartan decomposition in the inherited integral Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Pointwise
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Plancherel.RenardCartan
open Langlands.GeneralLinear

namespace Langlands.BruhatTits.SpecialCompact

namespace WeightBlocks

variable {N : ℕ} (w : Fin N → ℤ)

private abbrev Labels := ↥(Finset.univ.image w)

private def label (i : Fin N) : Labels w :=
  ⟨w i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩

private abbrev Index (b : Labels w) := {i : Fin N // label w i = b}

variable (A : Type*) [CommRing A]

private theorem diagonalBlock_mul {M P : Matrix (Fin N) (Fin N) A}
    (hM : ∀ i j, w i ≠ w j → M i j = 0) (b : Labels w) :
    (M * P).toBlock (fun i => label w i = b) (fun i => label w i = b) =
      M.toBlock (fun i => label w i = b) (fun i => label w i = b) *
        P.toBlock (fun i => label w i = b) (fun i => label w i = b) := by
  rw [Matrix.toBlock_mul_eq_add _ (fun i => label w i = b)]
  have hzero : M.toBlock (fun i => label w i = b) (fun i => label w i ≠ b) = 0 := by
    ext i j
    exact hM i j (fun h => j.property ((Subtype.ext h).symm.trans i.property))
  rw [hzero, Matrix.zero_mul, add_zero]

private def block (b : Labels w) :
    GeneralLinear.blockLeviSubgroup A w →* Matrix.GeneralLinearGroup (Index w b) A where
  toFun x :=
    { val := x.val.val.toBlock _ _
      inv := x.val.inv.toBlock _ _
      val_inv := by
        rw [← diagonalBlock_mul w A x.property, x.val.val_inv, Matrix.toBlock_one_self]
      inv_val := by
        have hinv := (GeneralLinear.blockLeviSubgroup A w).inv_mem x.property
        have h := diagonalBlock_mul w A (M := x.val.inv) (P := x.val.val) hinv b
        rw [← h, x.val.inv_val, Matrix.toBlock_one_self] }
  map_one' := Units.ext (Matrix.toBlock_one_self _)
  map_mul' x y := Units.ext (diagonalBlock_mul w A x.property b)

private theorem block_apply (b : Labels w) (g : GeneralLinear.blockLeviSubgroup A w)
    (i j : Index w b) : (block w A b g) i j = g.val i.val j.val :=
  rfl

private def assemble :
    (∀ b : Labels w, Matrix.GeneralLinearGroup (Index w b) A) →*
      Matrix.GeneralLinearGroup (Fin N) A :=
  (Langlands.GeneralLinear.reindex (R := A) (Equiv.sigmaFiberEquiv (label w))).toMonoidHom.comp
    ((Units.map (Matrix.blockDiagonal'RingHom (fun b : Labels w => Index w b) A).toMonoidHom).comp
      MulEquiv.piUnits.symm.toMonoidHom)

private theorem assemble_apply (g : ∀ b : Labels w, Matrix.GeneralLinearGroup (Index w b) A)
    {b c : Labels w} (i : Index w b) (j : Index w c) :
    assemble w A g i.val j.val = Matrix.blockDiagonal' (fun b => (g b).val) ⟨b, i⟩ ⟨c, j⟩ := by
  let e := Equiv.sigmaFiberEquiv (label w)
  change Matrix.blockDiagonal' (fun b => (g b).val) (e.symm i.val) (e.symm j.val) = _
  rw [show e.symm i.val = ⟨b, i⟩ from e.symm_apply_apply ⟨b, i⟩,
    show e.symm j.val = ⟨c, j⟩ from e.symm_apply_apply ⟨c, j⟩]

private theorem assemble_mem (g : ∀ b : Labels w, Matrix.GeneralLinearGroup (Index w b) A) :
    assemble w A g ∈ GeneralLinear.blockLeviSubgroup A w := by
  intro i j h
  rw [← show (⟨i, rfl⟩ : Index w (label w i)).val = i from rfl,
    ← show (⟨j, rfl⟩ : Index w (label w j)).val = j from rfl, assemble_apply]
  exact Matrix.blockDiagonal'_apply_ne (fun b => (g b).val) _ _
    (fun e => h (congrArg Subtype.val e))

private theorem blocks_injective :
    Function.Injective (fun g : GeneralLinear.blockLeviSubgroup A w => fun b => block w A b g) := by
  intro g h heq
  apply Subtype.ext
  apply Units.ext
  ext i j
  by_cases hij : w i = w j
  · let e : label w j = label w i := Subtype.ext hij.symm
    exact congrArg (fun x : Matrix.GeneralLinearGroup (Index w (label w i)) A =>
      x ⟨i, rfl⟩ ⟨j, e⟩) (congrFun heq (label w i))
  · rw [g.property i j hij, h.property i j hij]

private def blockEquiv :
    GeneralLinear.blockLeviSubgroup A w ≃* ∀ b : Labels w, Matrix.GeneralLinearGroup (Index w b) A where
  toFun g b := block w A b g
  invFun g := ⟨assemble w A g, assemble_mem w A g⟩
  left_inv g := by
    apply blocks_injective w A
    funext b
    apply Units.ext
    ext i j
    rw [block_apply, assemble_apply, Matrix.blockDiagonal'_apply_eq]
  right_inv g := by
    funext b
    apply Units.ext
    ext i j
    rw [block_apply, assemble_apply, Matrix.blockDiagonal'_apply_eq]
  map_mul' g h := funext fun b => map_mul (block w A b) g h

private abbrev Size (b : Labels w) := Fintype.card (Index w b)

private def blockOrder (a : Fin N → ℤ) (b : Labels w) : Fin (Size w b) ≃ Index w b :=
  let e := (Fintype.equivFin (Index w b)).symm
  (Tuple.sort fun k => -a (e k).val).trans e

private theorem blockOrder_strictAnti (a : Fin N → ℤ) (ha : Function.Injective a)
    (b : Labels w) : StrictAnti (fun k => a (blockOrder w a b k).val) := by
  let e := (Fintype.equivFin (Index w b)).symm
  have h := Tuple.monotone_sort (fun k => -a (e k).val)
  have hant : Antitone (fun k => a (blockOrder w a b k).val) :=
    fun _ _ hkl => neg_le_neg_iff.mp (h hkl)
  exact hant.strictAnti_iff_injective.mpr
    (ha.comp (Subtype.val_injective.comp (blockOrder w a b).injective))

private def sortedBlockEquiv (a : Fin N → ℤ) :
    GroupScheme.GeneralLinear.blockLeviSubgroup A w ≃*
      ∀ b : Labels w, Langlands.GeneralLinear (Size w b) A :=
  (blockEquiv w A).trans
    (MulEquiv.piCongrRight fun b => Langlands.GeneralLinear.reindex (R := A) (blockOrder w a b).symm)

private theorem sortedBlockEquiv_apply (a : Fin N → ℤ)
    (g : GroupScheme.GeneralLinear.blockLeviSubgroup A w)
    (b : Labels w) (i j : Fin (Size w b)) :
    sortedBlockEquiv w A a g b i j = g.val (blockOrder w a b i).val (blockOrder w a b j).val :=
  rfl

private theorem sortedBlockEquiv_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (a : Fin N → ℤ) (g : GroupScheme.GeneralLinear.blockLeviSubgroup A w) (b : Labels w) :
    sortedBlockEquiv w B a ⟨Matrix.GeneralLinearGroup.map f g.val,
      GroupScheme.GeneralLinear.map_mem_blockLeviSubgroup w f g.property⟩ b =
        Matrix.GeneralLinearGroup.map f (sortedBlockEquiv w A a g b) := by
  apply Units.ext
  rfl

private theorem mem_integral_sortedBlocks {F : Type u} [Field F] [ValuativeRel F]
    (a : Fin N → ℤ) (g : GroupScheme.GeneralLinear.blockLeviSubgroup F w) :
    g.val ∈ (GroupScheme.GeneralLinear.blockLeviSubgroup 𝒪[F] w).map
        (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[F] F)) ↔
      ∀ b, sortedBlockEquiv w F a g b ∈ Iwasawa.integralRange (ValuativeRel.valuation F) (Size w b) := by
  let f := algebraMap 𝒪[F] F
  constructor
  · rintro ⟨g₀, hg₀, hg⟩ b
    let z : GroupScheme.GeneralLinear.blockLeviSubgroup 𝒪[F] w := ⟨g₀, hg₀⟩
    have he : (⟨Matrix.GeneralLinearGroup.map f z.val,
      GroupScheme.GeneralLinear.map_mem_blockLeviSubgroup w f z.property⟩ :
        GroupScheme.GeneralLinear.blockLeviSubgroup F w) = g := Subtype.ext hg
    refine ⟨sortedBlockEquiv w 𝒪[F] a z b, ?_⟩
    exact (sortedBlockEquiv_map w f a z b).symm.trans
      (congrArg (fun g => sortedBlockEquiv w F a g b) he)
  · intro hg
    choose z hz using hg
    let g₀ := (sortedBlockEquiv w 𝒪[F] a).symm z
    refine ⟨g₀.val, g₀.property, ?_⟩
    have he : (⟨Matrix.GeneralLinearGroup.map f g₀.val,
        GroupScheme.GeneralLinear.map_mem_blockLeviSubgroup w f g₀.property⟩ :
          GroupScheme.GeneralLinear.blockLeviSubgroup F w) = g := by
      apply (sortedBlockEquiv w F a).injective
      funext b
      rw [sortedBlockEquiv_map]
      have hb : sortedBlockEquiv w 𝒪[F] a g₀ b = z b :=
        congrFun ((sortedBlockEquiv w 𝒪[F] a).apply_symm_apply z) b
      rw [hb]
      exact hz b
    exact congrArg Subtype.val he

end WeightBlocks

open WeightBlocks

set_option maxHeartbeats 1600000 in
/-- The Cartan decompositions of the weight blocks give disjoint and exhaustive
representatives in the actual standard Levi at its inherited integral subgroup. -/
theorem generalLinearIntegralLeviCartan : GeneralLinearIntegralLeviCartanStatement.{u} := by
  intro F _ _ _ _ N ν
  dsimp only
  intro hν J hJ
  let R := CommRingCat.of F
  let T := splitTorus.commGroupScheme (Spec R) (ULift (Fin N))
  let i := GroupScheme.GeneralLinear.diagonalTorus (Fin N) R
  let G := GroupScheme.GeneralLinear.groupScheme (Fin N) R
  let V := GroupScheme.GeneralLinear.cocharacterCoordEquiv (Fin N) F
  let K := (GroupScheme.GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)).integralPoints
  let L := Standard.leviScheme i ν J
  let j := Standard.leviHom i ν J
  let iL := Standard.leviTorusHom i ν J
  let f := rationalPoints.map j
  let KL := K.comap f
  let : IsAffineHom L.X.hom := (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
  let C := C0Plus T iL (positiveRelativeRoots iL ν)
  change Function.Bijective (fun a : C => DoubleCoset.mk KL KL a.val)
  have hG : IsConnectedReductive G := isConnectedReductive_generalLinear F (Fin N)
  have hi : IsMaximalSplitTorus i := GroupScheme.GeneralLinear.isMaximalSplitTorus_diagonalTorus F
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F G hG T i hi ν hν J hJ
  let w := V ζ
  let s := V ν
  let e := GroupScheme.GeneralLinear.rationalPointsEquiv N R
  have hrep := Standard.isRepresentedBy_leviHom i ν J
  obtain ⟨hblocks, hintegral⟩ := generalLinearStandardLeviIntegralPoints F N ν hν J ζ hζ
  let E := hrep.rationalPointsEquiv.trans
    (((e.subgroupMap (standardLeviPoints i ν J)).trans (MulEquiv.subgroupCongr hblocks)))
  have hE (m : rationalPoints L) : (E m).val = e (f m) := rfl
  let Q := E.trans (sortedBlockEquiv w F s)
  have hmem (m : rationalPoints L) :
      m ∈ KL ↔ ∀ b, Q m b ∈ Iwasawa.integralRange (ValuativeRel.valuation F) (Size w b) := by
    change _ ↔ ∀ b, sortedBlockEquiv w F s (E m) b ∈ _
    rw [← mem_integral_sortedBlocks w s (E m), hE, ← hintegral]
    constructor
    · intro hm
      exact ⟨f m, ⟨hm, (hrep.rationalPointsEquiv m).property⟩, rfl⟩
    · rintro ⟨x, hx, he⟩
      change f m ∈ K
      rw [← e.injective he]
      exact hx.1
  let point (c : cocharacterLattice T) :=
    rationalPoints.map iL (uniformizerSection T (Multiplicative.ofAdd c))
  let π := SplitTorusValuation.uniformizerUnit F
  let exponents (c : cocharacterLattice T) (b : Labels w) (k : Fin (Size w b)) :=
    V c (blockOrder w s b k).val
  have hpoint (c : cocharacterLattice T) (b : Labels w) :
      Q (point c) b = Iwasawa.torus π (exponents c b) := by
    have hmap : f (point c) =
        rationalPoints.map i (uniformizerSection T (Multiplicative.ofAdd c)) := by
      change (_ ≫ iL.hom.hom) ≫ j.hom.hom = _
      rw [Category.assoc, ← Grp.comp_hom_hom, Standard.leviTorusHom_comp i ν J]
      rfl
    have he : (E (point c)).val = Iwasawa.torus π (V c) := by
      rw [hE, hmap]
      exact rationalPointsEquiv_diagonalUniformizerSection F c
    apply Units.ext
    ext a d
    change sortedBlockEquiv w F s (E (point c)) b a d = _
    rw [sortedBlockEquiv_apply, he, Iwasawa.torus_val, Iwasawa.torus_val]
    by_cases had : a = d
    · subst d
      simp only [Matrix.diagonal_apply_eq]
      rfl
    · have hne : (blockOrder w s b a).val ≠ (blockOrder w s b d).val :=
        fun h => had ((blockOrder w s b).injective (Subtype.ext h))
      rw [Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ had]
  have hrepζ : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j := by
    rw [← (hcompare ζ hζ).2.1]
    exact hrep
  have hL := dynamicCentralizerReductive F G hG _ L j
    (Standard.isClosedSubgroup_leviHom i ν J) hrepζ
  let : Smooth G.X.hom := hG.smooth
  let : Smooth L.X.hom := hL.smooth
  have hroots := relativeRoots_centralizer_factor dynamicLie i iL j
    (Standard.leviTorusHom_comp i ν J) ζ hrepζ
  let rootsGL := GroupScheme.GeneralLinear.rootDatum (Fin N) F
  have hrange := (GroupScheme.GeneralLinear.isRootDatumOf_rootDatum (n := Fin N) F).2.1
  have hpos (r : {p : Fin N × Fin N // p.1 ≠ p.2}) :
      rootsGL.root r ∈ positiveRelativeRoots iL ν ↔
        w r.val.1 = w r.val.2 ∧ s r.val.2 < s r.val.1 := by
    have hmemRoot : rootsGL.root r ∈ relativeRoots i := by
      change rootsGL.root r ∈ roots i
      rw [← hrange]
      exact Set.mem_range_self _
    change (rootsGL.root r ∈ relativeRoots iL ∧ 0 < latticePairing T (rootsGL.root r) ν) ↔ _
    rw [hroots]
    change ((rootsGL.root r ∈ relativeRoots i ∧ latticePairing T (rootsGL.root r) ζ = 0) ∧
      0 < latticePairing T (rootsGL.root r) ν) ↔ _
    have hpair (c : cocharacterLattice T) :
        latticePairing T (rootsGL.root r) c = V c r.val.1 - V c r.val.2 :=
      GroupScheme.GeneralLinear.latticePairing_rootDatum_root_fintype F c r
    rw [hpair ζ, hpair ν, sub_eq_zero, sub_pos]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hmemRoot, h.1⟩, h.2⟩⟩
  have horder (b : Labels w) : StrictAnti (fun k => s (blockOrder w s b k).val) :=
    blockOrder_strictAnti w s
      ((GroupScheme.GeneralLinear.isGenericCocharacter_diagonalTorus_iff F ν).mp hν) b
  have hchamber (c : cocharacterLattice T) :
      (∀ α ∈ positiveRelativeRoots iL ν, 0 ≤ latticePairing T α c) ↔
        ∀ b, Antitone (exponents c b) := by
    constructor
    · intro hc b a d had
      rcases eq_or_lt_of_le had with rfl | had
      · exact le_rfl
      let a₀ := blockOrder w s b a
      let d₀ := blockOrder w s b d
      let r : {p : Fin N × Fin N // p.1 ≠ p.2} :=
        ⟨(a₀.val, d₀.val), fun h => had.ne ((blockOrder w s b).injective (Subtype.ext h))⟩
      have hl : w a₀.val = w d₀.val :=
        congrArg Subtype.val (a₀.property.trans d₀.property.symm)
      have hα := hc _ ((hpos r).mpr ⟨hl, horder b had⟩)
      rw [GroupScheme.GeneralLinear.latticePairing_rootDatum_root_fintype] at hα
      exact sub_nonneg.mp hα
    · intro hc α hα
      have hmem : α ∈ roots i := ((hroots ▸ hα.1).1)
      rw [← hrange] at hmem
      obtain ⟨r, rfl⟩ := hmem
      obtain ⟨hw, hs⟩ := (hpos r).mp hα
      let b := label w r.val.1
      obtain ⟨a, ha⟩ := (blockOrder w s b).surjective ⟨r.val.1, rfl⟩
      obtain ⟨d, hd⟩ := (blockOrder w s b).surjective ⟨r.val.2, Subtype.ext hw.symm⟩
      have ha' : (blockOrder w s b a).val = r.val.1 := congrArg Subtype.val ha
      have hd' : (blockOrder w s b d).val = r.val.2 := congrArg Subtype.val hd
      have had : a < d := (horder b).lt_iff_gt.mp (by simpa only [ha', hd'] using hs)
      rw [GroupScheme.GeneralLinear.latticePairing_rootDatum_root_fintype, ← ha', ← hd']
      exact sub_nonneg.mpr (hc b had.le)
  let index : (Σ b : Labels w, Fin (Size w b)) ≃ Fin N :=
    (Equiv.sigmaCongrRight (blockOrder w s)).trans (Equiv.sigmaFiberEquiv (label w))
  have hπ := uniformizerUnit_isUniformizingElement F
  constructor
  · intro a b hab
    obtain ⟨c, hc, hca⟩ := (mem_C0Plus T iL _ a.val).mp a.property
    obtain ⟨d, hd, hdb⟩ := (mem_C0Plus T iL _ b.val).mp b.property
    obtain ⟨k, hk, l, hl, heq⟩ := DoubleCoset.eq.mp hab
    have hweight (r : Labels w) : exponents c r = exponents d r := by
      have h : Iwasawa.torus π (exponents d r) =
          Q k r * Iwasawa.torus π (exponents c r) * Q l r := by
        have he : Q (point d) r = Q k r * Q (point c) r * Q l r := by
          rw [show point d = b.val from hdb, show point c = a.val from hca]
          simpa only [map_mul, Pi.mul_apply] using congrArg (fun m => Q m r) heq
        rwa [hpoint, hpoint] at he
      exact Cartan.exponent_unique hπ ((hchamber c).mp hc r) ((hchamber d).mp hd r)
        ((hmem k).mp hk r) ((hmem l).mp hl r) (one_mem _) (one_mem _)
        (by simpa using h.symm)
    have hcd : c = d := V.injective (funext fun a => by
      obtain ⟨⟨r, k⟩, rfl⟩ := index.surjective a
      exact congrFun (hweight r) k)
    exact Subtype.ext (hca.symm.trans ((congrArg point hcd).trans hdb))
  · intro q
    induction q using _root_.Quotient.inductionOn with
    | h g =>
      choose a ha k hk l hl hg using fun b : Labels w =>
        Cartan.exists_cartan hπ (Size w b) (Q g b)
      let c := GroupScheme.GeneralLinear.cocharacterOfWeights F
        ((fun y : Σ b : Labels w, Fin (Size w b) => a y.1 y.2) ∘ index.symm)
      have hw (b : Labels w) : exponents c b = a b := by
        have hwc := GroupScheme.GeneralLinear.cocharacterCoordEquiv_cocharacterOfWeights F
          ((fun y : Σ b : Labels w, Fin (Size w b) => a y.1 y.2) ∘ index.symm)
        funext t
        change V c (index ⟨b, t⟩) = _
        rw [show V c = _ from hwc]
        change a (index.symm (index ⟨b, t⟩)).1 (index.symm (index ⟨b, t⟩)).2 = a b t
        rw [Equiv.symm_apply_apply]
      refine ⟨⟨point c, (mem_C0Plus T iL _ _).mpr ⟨c,
        (hchamber c).mpr (fun b => (hw b).symm ▸ ha b), rfl⟩⟩, DoubleCoset.eq.mpr ?_⟩
      refine ⟨Q.symm k, (hmem _).mpr ?_, Q.symm l, (hmem _).mpr ?_, Q.injective ?_⟩
      · intro b
        rw [MulEquiv.apply_symm_apply]
        exact hk b
      · intro b
        rw [MulEquiv.apply_symm_apply]
        exact hl b
      · funext b
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
        change Q g b = k b * Q (point c) b * l b
        rw [hpoint, hw]
        exact hg b

end Langlands.BruhatTits.SpecialCompact
