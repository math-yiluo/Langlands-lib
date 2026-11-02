import Langlands.AlgebraicGeometry.Picard.LinearSystemBaseLocusBezoutStatement
import Langlands.AlgebraicGeometry.Picard.SectionCokernelEulerCoefficientProof
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Langlands.AlgebraicGeometry.Picard.AffineGenerationLocusIntersectionProof
import Langlands.AlgebraicGeometry.Modules.CoherentIntegralIdealFiltrationProof
import Langlands.AlgebraicGeometry.Modules.AmpleCoherentEulerCoefficientProof
import Langlands.AlgebraicGeometry.Picard.SectionCutDimensionProof
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.JacobsonSpace
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Data.Set.Card.Arithmetic

/-! # The Bezout count for a section against a linear system with finite base locus -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology Order

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules
  Langlands.AlgebraicGeometry.Modules
  Langlands.AlgebraicGeometry.Modules.DerivedSections

local instance (X : Scheme.{u}) : (structureModule X).IsQuasicoherent :=
  (LineBundle.trivial X).property.isQuasicoherent

local instance (X : Scheme.{u}) : (structureSheaf X).IsQuasicoherent :=
  (LineBundle.trivial X).property.isQuasicoherent

local instance {X : Scheme.{u}} (L : LineBundle X) (n : ℕ) :
    (tensorPow L.obj n).IsQuasicoherent :=
  (tensorPow_isLocallyFreeRankOne X L n).isQuasicoherent

local instance {X : Scheme.{u}} (L : LineBundle X) (n : ℕ) (s : L.powSections n) :
    (cokernel (sectionHom (tensorPow L.obj n) s)).IsQuasicoherent :=
  QuasicoherentLocal.isQuasicoherent_cokernel (sectionHom (tensorPow L.obj n) s)

namespace LinearSystemBaseLocusBezout

/-- An inducing map of schemes reflects and preserves the specialization order. -/
lemma le_iff_of_isInducing {X Y : Scheme.{u}} {f : X → Y} (hf : IsInducing f) (a b : X) :
    f a ≤ f b ↔ a ≤ b := by
  rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
  exact hf.specializes_iff

/-- An inducing map of schemes is strictly monotone for the specialization order. -/
lemma strictMono_of_isInducing {X Y : Scheme.{u}} {f : X → Y} (hf : IsInducing f) :
    StrictMono f := fun a b hab => by
  rw [lt_iff_le_not_ge] at hab ⊢
  rw [le_iff_of_isInducing hf, le_iff_of_isInducing hf]
  exact hab

/-- A strict chain of generizations whose most generic member lies in the closed
range of a closed embedding lifts to the source, so the lifted starting point has
coheight at least the length of the chain. -/
theorem exists_lift_le_coheight {W Z : Scheme.{u}} {i : W → Z} (hi : IsClosedEmbedding i)
    (p : LTSeries Z) (hp : p.last ∈ Set.range i) :
    ∃ w : W, i w = p.head ∧ (p.length : ℕ∞) ≤ coheight w := by
  have hmem : ∀ k, p k ∈ Set.range i := fun k =>
    (Scheme.le_iff_specializes.mp (p.monotone (Fin.le_last k))).mem_closed
      hi.isClosed_range hp
  choose w hw using hmem
  have hmono : StrictMono w := by
    intro k l hkl
    have h := p.strictMono hkl
    rw [← hw k, ← hw l] at h
    rw [lt_iff_le_not_ge] at h ⊢
    rwa [le_iff_of_isInducing hi.isInducing, le_iff_of_isInducing hi.isInducing] at h
  let q : LTSeries W := LTSeries.mk p.length w hmono
  refine ⟨q.head, hw 0, ?_⟩
  exact length_le_coheight_head (p := q)

/-- Krull's principal ideal theorem on an affine chart: a point of the zero locus of a
line-bundle section whose coheight is at least `d + 1` is the start of a strict chain of
generizations of length `d` whose most generic member still lies in the zero locus. -/
theorem exists_series_of_not_mem_trivializationOpen {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (N : LineBundle Z) (u : GlobalSections N.obj) (x : Z)
    (hx : x ∉ trivializationOpen N.obj u) (d : ℕ)
    (hd : ((d + 1 : ℕ) : ℕ∞) ≤ coheight x) :
    ∃ p : LTSeries Z, p.head = x ∧ p.length = d ∧ p.last ∉ trivializationOpen N.obj u := by
  obtain ⟨W, hxW, ⟨t⟩⟩ := N.property x
  obtain ⟨V, hV, hxV, hVW⟩ :=
    (Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens) hxW
  change Z.Opens at V
  let tV : N.obj.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback V.ι).app N.obj ≪≫
      pullbackTrivializationOfLE hVW N.obj t
  obtain ⟨a, ha⟩ := exists_inf_trivializationOpen_eq_basicOpen N u V tV
  have hVa : IsAffineOpen V := hV
  have : IsNoetherianRing Γ(Z, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let P : Spec Γ(Z, V) := hVa.primeIdealOf ⟨x, hxV⟩
  have hPx : hVa.fromSpec P = x := hVa.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hzero : ∀ y : Z, y ∈ V → y ∉ Z.basicOpen a → y ∉ trivializationOpen N.obj u := by
    intro y hyV hya hyt
    apply hya
    have : y ∈ V ⊓ trivializationOpen N.obj u := ⟨hyV, hyt⟩
    rwa [ha] at this
  have hxa : x ∉ Z.basicOpen a := fun h => hx (by
    have : x ∈ V ⊓ trivializationOpen N.obj u := by rw [ha]; exact h
    exact this.2)
  have hbasic : ∀ Q : Spec Γ(Z, V), hVa.fromSpec Q ∈ Z.basicOpen a ↔ a ∉ Q.asIdeal := by
    intro Q
    change Q ∈ hVa.fromSpec ⁻¹ᵁ Z.basicOpen a ↔ _
    rw [hVa.fromSpec_preimage_basicOpen]
    exact PrimeSpectrum.mem_basicOpen _ _
  have haP : a ∈ P.asIdeal := by
    by_contra h
    exact hxa (hPx ▸ (hbasic P).2 h)
  have hcoh : coheight x = coheight P := by
    rw [← hPx]
    exact coheight_eq_of_isOpenImmersion hVa.fromSpec
  have hheight : ((d + 1 : ℕ) : ℕ∞) ≤ P.asIdeal.height := by
    rw [idealHeight_eq_coheight, ← hcoh]
    exact hd
  let I : Ideal Γ(Z, V) := Ideal.span {a}
  have hIP : I ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 haP
  let π : Γ(Z, V) ⟶ CommRingCat.of (Γ(Z, V) ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let P' : Spec (CommRingCat.of (Γ(Z, V) ⧸ I)) :=
    ⟨P.asIdeal.map (Ideal.Quotient.mk I), Ideal.isPrime_map_quotientMk_of_isPrime hIP⟩
  have hkrull : P.asIdeal.height ≤ P'.asIdeal.height + 1 :=
    Ideal.height_le_height_add_one_of_mem haP
  have hP' : (d : ℕ∞) ≤ coheight P' := by
    rw [← idealHeight_eq_coheight]
    have h := hheight.trans hkrull
    push_cast at h
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 h
  obtain ⟨q, hqhead, hqlen⟩ := exists_series_of_le_coheight P' hP'
  let g : Spec (CommRingCat.of (Γ(Z, V) ⧸ I)) → Z := fun y => hVa.fromSpec (Spec.map π y)
  have hg : IsInducing g :=
    hVa.fromSpec.isOpenEmbedding.isInducing.comp (Spec.map π).isClosedEmbedding.isInducing
  have hgP' : g P' = x := by
    rw [← hPx]
    change hVa.fromSpec (PrimeSpectrum.comap (Ideal.Quotient.mk I) P') = _
    congr 1
    exact PrimeSpectrum.ext (Ideal.comap_map_mk hIP)
  refine ⟨q.map g (strictMono_of_isInducing hg), ?_, ?_, ?_⟩
  · rw [LTSeries.head_map, hqhead, hgP']
  · rw [LTSeries.map_length, hqlen]
  · rw [LTSeries.last_map]
    apply hzero
    · show _ ∈ (V : Set Z)
      rw [← hVa.range_fromSpec]
      exact ⟨_, rfl⟩
    · intro h
      have h0 : Ideal.Quotient.mk I a = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
      have hmem : a ∈ (Spec.map π q.last).asIdeal := by
        change Ideal.Quotient.mk I a ∈ (q.last : PrimeSpectrum (Γ(Z, V) ⧸ I)).asIdeal
        rw [h0]
        exact zero_mem _
      exact (hbasic _).1 h hmem

/-- The coheight of a point of a scheme is bounded by the topological Krull dimension. -/
lemma coheight_le_topologicalKrullDim (X : Scheme.{u}) (x : X) :
    (coheight x : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  have h : ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
    rw [ringKrullDim_stalk_eq_coheight]
    simpa only [topologicalKrullDim, coheight_orderIso] using
      (coheight_le_krullDim ((irreducibleSetEquivPoints (α := X)).symm x))
  rwa [ringKrullDim_stalk_eq_coheight] at h

/-- The structure sheaf of an integral scheme is not zero. -/
lemma not_isZero_structureSheaf (X : Scheme.{u}) [IsIntegral X] :
    ¬ IsZero (structureSheaf X) := by
  intro h
  let one : Γ(X, ⊤) := 1
  have h1 := congrArg (fun g : structureSheaf X ⟶ structureSheaf X =>
    g.app ⊤ (show Γ(structureSheaf X, ⊤) from one)) (h.eq_of_src (𝟙 _) 0)
  simp only [Scheme.Modules.Hom.id_app, Scheme.Modules.Hom.zero_app] at h1
  exact one_ne_zero (α := Γ(X, ⊤)) h1

/-- The stalk support of the final term of a coherent filtration lies in the union of
the stalk supports of its graded factors. -/
lemma stalkSupport_last_subset {X : Scheme.{u}} {n : ℕ} (F : CoherentFiltration X n) :
    stalkSupport (F.term (Fin.last n)) ⊆ ⋃ j, stalkSupport (F.factor j) := by
  have h : ∀ k : Fin (n + 1), stalkSupport (F.term k) ⊆ ⋃ j, stalkSupport (F.factor j) := by
    intro k
    induction k using Fin.induction with
    | zero =>
        rw [stalkSupport_eq_empty_iff.2 F.zero]
        exact Set.empty_subset _
    | succ k ih =>
        have hk := stalkSupport_shortExact (F.complex k) (F.complex_shortExact k)
        change stalkSupport (F.term k.succ) =
          stalkSupport (F.term k.castSucc) ∪ stalkSupport (F.factor k) at hk
        rw [hk]
        exact Set.union_subset ih (Set.subset_iUnion (fun j => stalkSupport (F.factor j)) k)
  exact h (Fin.last n)

/-- The cokernel of a section map that generates somewhere on an integral scheme of
dimension at most `d + 1` has support dimension at most `d`. -/
lemma hasSupportDimensionLT_sectionHom_cokernel {X : Scheme.{u}} [IsIntegral X] (d : ℕ)
    (hX : topologicalKrullDim X ≤ ((d + 1 : ℕ) : WithBot ℕ∞))
    (N : LineBundle X) (u : GlobalSections N.obj)
    (hu : (trivializationOpen N.obj u : Set X).Nonempty) :
    HasSupportDimensionLT (cokernel (sectionHom N.obj u)) (d + 1) := by
  rw [hasSupportDimensionLT_iff_supportDimension, supportDimension_sectionHom_cokernel N u hu]
  apply ENat.WithBot.add_one_le_natCast_iff.mp
  refine le_trans ?_ hX
  obtain ⟨y, hy⟩ := hu
  exact topologicalKrullDim_add_one_le_of_isClosed {x : X | x ∉ trivializationOpen N.obj u}
    (trivializationOpen N.obj u).isOpen.isClosed_compl
    (fun h => Set.eq_univ_iff_forall.mp h y hy)

/-- The induction statement: on an integral proper scheme of dimension at most `d`, the
number of base-locus points of coheight at least `d` is at most
`d! * q ^ d` times the degree-`d` coefficient of the line-bundle Euler polynomial. -/
def BezoutCountInDimension (d : ℕ) : Prop :=
  ∀ (K : Type u) [Field K] (Z : Scheme.{u}) [IsIntegral Z] [IsNoetherian Z] [Z.IsSeparated]
    (f : Z ⟶ Spec (CommRingCat.of K)) [IsProper f],
    topologicalKrullDim Z ≤ d →
    ∀ (N : LineBundle Z) (q : ℕ) (S : Set (N.powSections q)),
      {x : Z | ∀ t ∈ S, x ∉ N.sectionOpen t}.Finite →
      ({x : Z | (∀ t ∈ S, x ∉ N.sectionOpen t) ∧ (d : ℕ∞) ≤ coheight x}.ncard : ℚ) ≤
        (d.factorial : ℚ) * (q : ℚ) ^ d * (lineBundleEulerPolynomial f N d).coeff d

/-- One integral piece of the filtered cokernel: the inductive bound on the piece, with the
sections pulled back, expressed through the piece's coherent Euler coefficient. -/
theorem ncard_piece_le (d : ℕ) (ih : BezoutCountInDimension.{u} d)
    (K : Type u) [Field K] (Z : Scheme.{u}) [IsNoetherian Z] [Z.IsSeparated]
    (f : Z ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (W : Scheme.{u}) (i : W ⟶ Z) [IsClosedImmersion i] [IsIntegral W]
    (I : W.Modules) [I.IsQuasicoherent] (hI : HasFiniteAffineSections I)
    (ι : I ⟶ structureModule W) [Mono ι] (hne : ¬ IsZero I)
    (hP : HasFiniteAffineSections ((Scheme.Modules.pushforward i).obj I))
    (hdim : HasSupportDimensionLT ((Scheme.Modules.pushforward i).obj I) (d + 1))
    (N : LineBundle Z) (q : ℕ) (S : Set (N.powSections q))
    (hB : {x : Z | ∀ t ∈ S, x ∉ N.sectionOpen t}.Finite) :
    letI := QuasicoherentLocal.isQuasicoherent_pushforward i I
    ({w : W | (∀ t ∈ S, i w ∉ N.sectionOpen t) ∧ (d : ℕ∞) ≤ coheight w}.ncard : ℚ) ≤
      (d.factorial : ℚ) * (q : ℚ) ^ d *
        (coherentEulerPolynomial f ((Scheme.Modules.pushforward i).obj I) hP N d).coeff d := by
  let : ((Scheme.Modules.pushforward i).obj I).IsQuasicoherent :=
    QuasicoherentLocal.isQuasicoherent_pushforward i I
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian i
  let : CompactSpace W := i.isClosedEmbedding.compactSpace
  let : IsNoetherian W := ⟨⟩
  let : W.IsSeparated := ⟨by
    rw [← terminal.comp_from i]
    infer_instance⟩
  have hWdim : topologicalKrullDim W ≤ (d : WithBot ℕ∞) := by
    have h := (hasSupportDimensionLT_pushforward_iff i i.isClosedEmbedding I (d + 1)).mp hdim
    rw [hasSupportDimensionLT_iff_supportDimension, supportDimension_ideal W I ι hne] at h
    exact ENat.WithBot.lt_add_one_iff.mp (by simpa only [Nat.cast_add, Nat.cast_one] using h)
  let N' : LineBundle W := (LineBundle.pullback i).obj N
  let S' : Set (N'.powSections q) := (N.pullbackPowSection i) '' S
  have hmem : ∀ w : W, (∀ t ∈ S', w ∉ N'.sectionOpen t) ↔ ∀ t ∈ S, i w ∉ N.sectionOpen t := by
    intro w
    simp only [S', Set.forall_mem_image, N', LineBundle.sectionOpen_pullbackPowSection]
    rfl
  have hB' : {w : W | ∀ t ∈ S', w ∉ N'.sectionOpen t}.Finite := by
    refine (hB.preimage i.isClosedEmbedding.injective.injOn).subset ?_
    intro w hw
    exact (hmem w).1 hw
  have h := ih K W (i ≫ f) hWdim N' q S' hB'
  have hcoeff :
      (coherentEulerPolynomial f ((Scheme.Modules.pushforward i).obj I) hP N d).coeff d =
        (lineBundleEulerPolynomial (i ≫ f) N' d).coeff d := by
    rw [coherentEulerPolynomial_pushforward f i I hI hP N d]
    exact coherentEulerPolynomial_ideal_coeff_eq_structureModule (i ≫ f) I hI ι hne N' d hWdim
  rw [hcoeff]
  have hset : {w : W | (∀ t ∈ S, i w ∉ N.sectionOpen t) ∧ (d : ℕ∞) ≤ coheight w} =
      {w : W | (∀ t ∈ S', w ∉ N'.sectionOpen t) ∧ (d : ℕ∞) ≤ coheight w} := by
    ext w
    simp only [Set.mem_ofPred_eq, hmem]
  rw [hset]
  exact h

/-- The cut step: cutting an integral scheme of dimension at most `d + 1` by a power
section that generates somewhere bounds the base-locus points on its zero locus of
coheight at least `d + 1`. -/
theorem ncard_le_of_cut (d : ℕ) (ih : BezoutCountInDimension.{u} d)
    (K : Type u) [Field K] (Z : Scheme.{u}) [IsIntegral Z] [IsNoetherian Z] [Z.IsSeparated]
    (f : Z ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (hZ : topologicalKrullDim Z ≤ ((d + 1 : ℕ) : WithBot ℕ∞))
    (N : LineBundle Z) (r : ℕ) (u : N.powSections r)
    (hu : (N.sectionOpen u : Set Z).Nonempty)
    (q : ℕ) (S : Set (N.powSections q))
    (hB : {x : Z | ∀ t ∈ S, x ∉ N.sectionOpen t}.Finite) :
    ({x : Z | (∀ t ∈ S, x ∉ N.sectionOpen t) ∧ x ∉ N.sectionOpen u ∧
        ((d + 1 : ℕ) : ℕ∞) ≤ coheight x}.ncard : ℚ) ≤
      (d.factorial : ℚ) * (q : ℚ) ^ d *
        (((d + 1 : ℕ) : ℚ) * (r : ℚ) * (lineBundleEulerPolynomial f N (d + 1)).coeff (d + 1)) := by
  classical
  let Nr : LineBundle Z := ⟨tensorPow N.obj r, tensorPow_isLocallyFreeRankOne Z N r⟩
  let C := cokernel (sectionHom (tensorPow N.obj r) u)
  have hC : HasFiniteAffineSections C :=
    (hasFiniteAffineSections_lineBundle Nr).cokernel (sectionHom Nr.obj u)
  have hCdim : HasSupportDimensionLT C (d + 1) :=
    hasSupportDimensionLT_sectionHom_cokernel d hZ Nr u hu
  have heq := sectionCokernelEulerCoefficient K Z f d
    (by simpa only [Nat.cast_add, Nat.cast_one] using hZ) N r u hu hC hCdim
  obtain ⟨n, T, h0, ⟨iM⟩, hcoh, hstep⟩ := coherentIntegralIdealFiltration Z C inferInstance hC
  choose W i hi hW I ι hι hIc hI hne α β hcomp hshort using hstep
  let F : CoherentFiltration Z n :=
    { term := T
      factor := fun j => (Scheme.Modules.pushforward (i j)).obj (I j)
      zero := h0
      inclusion := α
      projection := β
      comp_zero := hcomp
      shortExact := hshort
      term_quasicoherent := fun j => (hcoh j).1
      term_finite := fun j => (hcoh j).2
      factor_quasicoherent := fun j => by
        let : IsClosedImmersion (i j) := hi j
        let : (I j).IsQuasicoherent := hIc j
        exact QuasicoherentLocal.isQuasicoherent_pushforward (i j) (I j)
      factor_finite := fun j => by
        let : IsClosedImmersion (i j) := hi j
        exact (hI j).pushforward (i j) }
  have hfactor : ∀ j, HasSupportDimensionLT (F.factor j) (d + 1) :=
    (F.hasSupportDimensionLT_iff (d + 1)).mp (hCdim.of_iso iM.symm)
  have : ∀ j, (F.factor j).IsQuasicoherent := F.factor_quasicoherent
  have hsum : (coherentEulerPolynomial f C hC N d).coeff d =
      ∑ j, (coherentEulerPolynomial f (F.factor j) (F.factor_finite j) N d).coeff d := by
    rw [F.coherentEulerPolynomial_eq_sum f C hC iM N d]
    exact Polynomial.finsetSum_coeff _ _ _
  let A : ∀ j, Set (W j) := fun j =>
    {w : W j | (∀ t ∈ S, i j w ∉ N.sectionOpen t) ∧ (d : ℕ∞) ≤ coheight w}
  have hsub : {x : Z | (∀ t ∈ S, x ∉ N.sectionOpen t) ∧ x ∉ N.sectionOpen u ∧
        ((d + 1 : ℕ) : ℕ∞) ≤ coheight x} ⊆ ⋃ j, (i j) '' A j := by
    rintro x ⟨hxS, hxu, hxd⟩
    obtain ⟨p, hphead, hplen, hplast⟩ :=
      exists_series_of_not_mem_trivializationOpen Nr u x hxu d hxd
    have hlastC : p.last ∈ stalkSupport C := by
      rw [show stalkSupport C = _ from stalkSupport_sectionHom_cokernel_eq Nr u hu]
      exact hplast
    have hlastT : p.last ∈ stalkSupport (F.term (Fin.last n)) := by
      rw [show stalkSupport (F.term (Fin.last n)) = stalkSupport C from
        stalkSupport_eq_of_iso iM]
      exact hlastC
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (stalkSupport_last_subset F hlastT)
    have : IsClosedImmersion (i j) := hi j
    have hjr : p.last ∈ Set.range (i j) := by
      rw [show stalkSupport (F.factor j) = _ from
        stalkSupport_pushforward (i j) (i j).isClosedEmbedding (I j)] at hj
      obtain ⟨w, -, hw⟩ := hj
      exact ⟨w, hw⟩
    obtain ⟨w, hw, hwd⟩ := exists_lift_le_coheight (i j).isClosedEmbedding p hjr
    refine Set.mem_iUnion.mpr ⟨j, w, ⟨?_, ?_⟩, ?_⟩
    · rw [hw, hphead]
      exact hxS
    · rw [← hplen]
      exact hwd
    · rw [hw, hphead]
  have hfinU : (⋃ j, (i j) '' A j).Finite := by
    refine hB.subset ?_
    intro x hx
    obtain ⟨j, w, hw, rfl⟩ := Set.mem_iUnion.mp hx
    exact hw.1
  have hinj : ∀ j, Function.Injective (i j) := fun j => by
    have : IsClosedImmersion (i j) := hi j
    exact (i j).isClosedEmbedding.injective
  have hpiece : ∀ j, ((A j).ncard : ℚ) ≤ (d.factorial : ℚ) * (q : ℚ) ^ d *
      (coherentEulerPolynomial f (F.factor j) (F.factor_finite j) N d).coeff d := fun j => by
    have : IsClosedImmersion (i j) := hi j
    have : IsIntegral (W j) := hW j
    have : (I j).IsQuasicoherent := hIc j
    have : Mono (ι j) := hι j
    exact ncard_piece_le d ih K Z f (W j) (i j) (I j) (hI j) (ι j) (hne j)
      (F.factor_finite j) (hfactor j) N q S hB
  calc (_ : ℚ) ≤ ((⋃ j, (i j) '' A j).ncard : ℚ) := by
        exact_mod_cast Set.ncard_le_ncard hsub hfinU
    _ ≤ ∑ j, (((i j) '' A j).ncard : ℚ) := by
        exact_mod_cast Set.ncard_iUnion_le_of_fintype _
    _ = ∑ j, ((A j).ncard : ℚ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Set.ncard_image_of_injective _ (hinj j)]
    _ ≤ ∑ j, (d.factorial : ℚ) * (q : ℚ) ^ d *
          (coherentEulerPolynomial f (F.factor j) (F.factor_finite j) N d).coeff d :=
        Finset.sum_le_sum fun j _ => hpiece j
    _ = _ := by
        rw [← Finset.mul_sum, ← hsum, heq]

/-- The base case: an integral scheme of dimension zero is a single point, and the
coefficient is the positive Euler characteristic of the structure sheaf. -/
theorem bezoutCountInDimension_zero : BezoutCountInDimension.{u} 0 := by
  intro K _ Z _ _ _ f _ hZ N q S _
  have hgen : ∀ x : Z, x = genericPoint Z := by
    intro x
    have h : coheight x ≤ 0 := by
      have h := (coheight_le_topologicalKrullDim Z x).trans hZ
      exact_mod_cast h
    have hle : x ≤ genericPoint Z :=
      Scheme.le_iff_specializes.mpr (genericPoint_specializes x)
    have hge := (Order.coheight_eq_zero.mp (nonpos_iff_eq_zero.mp h)) hle
    exact ((Scheme.le_iff_specializes.mp hge).antisymm (genericPoint_specializes x)).eq
  have : Subsingleton Z := ⟨fun a b => (hgen a).trans (hgen b).symm⟩
  have hS : HasSupportDimensionLT (structureSheaf Z) 1 := by
    simpa using HasSupportDimensionLT.of_topologicalKrullDim_le hZ (structureSheaf Z)
  have hpos := (coherentEulerCharacteristic_pos_iff_of_supportDimensionLT_one f
    (structureSheaf Z) (hasFiniteAffineSections_structureSheaf Z) hS).mpr
    (not_isZero_structureSheaf Z)
  have hcoeff : (lineBundleEulerPolynomial f N 0).coeff 0 =
      (coherentEulerCharacteristic f (structureSheaf Z)
        (hasFiniteAffineSections_structureSheaf Z) : ℚ) := by
    rw [lineBundleEulerPolynomial, coherentEulerPolynomial_zero_eq_C,
      coherentEulerConstantPolynomial, Polynomial.coeff_C_zero]
  rw [hcoeff, Nat.factorial_zero, pow_zero, Nat.cast_one, one_mul, one_mul]
  have h1 : (1 : ℤ) ≤ coherentEulerCharacteristic f (structureSheaf Z)
      (hasFiniteAffineSections_structureSheaf Z) := by
    omega
  calc (_ : ℚ) ≤ 1 := by exact_mod_cast Set.ncard_le_one_of_subsingleton _
    _ ≤ _ := by exact_mod_cast h1

/-- The inductive step: either a member of the linear system generates somewhere and the cut
step applies to it, or the whole scheme is the finite base locus and has dimension zero. -/
theorem bezoutCountInDimension_succ (d : ℕ) (ih : BezoutCountInDimension.{u} d) :
    BezoutCountInDimension.{u} (d + 1) := by
  intro K _ Z _ _ _ f _ hZ N q S hB
  by_cases hS : ∃ t ∈ S, (N.sectionOpen t : Set Z).Nonempty
  · obtain ⟨t, htS, ht⟩ := hS
    have h := ncard_le_of_cut d ih K Z f hZ N q t ht q S hB
    have hset : {x : Z | (∀ t ∈ S, x ∉ N.sectionOpen t) ∧ ((d + 1 : ℕ) : ℕ∞) ≤ coheight x} =
        {x : Z | (∀ t ∈ S, x ∉ N.sectionOpen t) ∧ x ∉ N.sectionOpen t ∧
          ((d + 1 : ℕ) : ℕ∞) ≤ coheight x} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨h.1, h.1 t htS, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [hset]
    refine h.trans (le_of_eq ?_)
    rw [Nat.factorial_succ]
    push_cast
    ring
  · have huniv : {x : Z | ∀ t ∈ S, x ∉ N.sectionOpen t} = Set.univ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro t ht hx
      exact hS ⟨t, ht, x, hx⟩
    have : Finite Z := Set.finite_univ_iff.mp (by rw [← huniv]; exact hB)
    have : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace f
    have hdim0 : topologicalKrullDim Z ≤ ((0 : ℕ) : WithBot ℕ∞) := by
      simpa using topologicalKrullDim_zero_of_discreteTopology Z
    have hempty : {x : Z | (∀ t ∈ S, x ∉ N.sectionOpen t) ∧
        ((d + 1 : ℕ) : ℕ∞) ≤ coheight x} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ hx
      have h : coheight x ≤ 0 := by
        have h := (coheight_le_topologicalKrullDim Z x).trans hdim0
        exact_mod_cast h
      have h' := hx.trans h
      norm_cast at h'
    have hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞) :=
      hdim0.trans (by exact_mod_cast Nat.zero_le d)
    have hcoeff : (lineBundleEulerPolynomial f N (d + 1)).coeff (d + 1) = 0 :=
      coherentEulerPolynomial_coeff_eq_zero_of_supportDimensionLT f _ _ N (d + 1)
        (HasSupportDimensionLT.of_topologicalKrullDim_le hd _)
    rw [hempty, hcoeff, Set.ncard_empty]
    simp

/-- The induction statement holds in every dimension. -/
theorem bezoutCountInDimension (d : ℕ) : BezoutCountInDimension.{u} d := by
  induction d with
  | zero => exact bezoutCountInDimension_zero
  | succ d ih => exact bezoutCountInDimension_succ d ih

end LinearSystemBaseLocusBezout

open LinearSystemBaseLocusBezout in
/-- The Bezout count for a section against a linear system with finite base locus. -/
theorem linearSystemBaseLocusBezout : LinearSystemBaseLocusBezoutStatement.{u} := by
  intro K _ _ X _ _ _ f _ e he hX L p q s S hs hB hdim
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
  have h := ncard_le_of_cut d (bezoutCountInDimension d) K X f hX L p s hs q S hB
  have hset : {x : X | (∀ t ∈ S, x ∉ L.sectionOpen t) ∧ x ∉ L.sectionOpen s} =
      {x : X | (∀ t ∈ S, x ∉ L.sectionOpen t) ∧ x ∉ L.sectionOpen s ∧
        ((d + 1 : ℕ) : ℕ∞) ≤ coheight x} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    refine ⟨fun hx => ⟨hx.1, hx.2, ?_⟩, fun hx => ⟨hx.1, hx.2.1⟩⟩
    have hx' := hdim x hx.1 hx.2
    rw [ringKrullDim_stalk_eq_coheight] at hx'
    exact_mod_cast hx'.ge
  have hcard : Nat.card {x : X // (∀ t ∈ S, x ∉ L.sectionOpen t) ∧ x ∉ L.sectionOpen s} =
      {x : X | (∀ t ∈ S, x ∉ L.sectionOpen t) ∧ x ∉ L.sectionOpen s}.ncard :=
    Nat.card_coe_set_eq _
  rw [hcard, hset]
  refine h.trans (le_of_eq ?_)
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  ring

end Langlands.AlgebraicGeometry.Picard
