import Langlands.GroupScheme.Rational.EvenChainCrossCoordinates
import Langlands.GroupScheme.Rational.SteinbergRationalBijection
import Langlands.GroupScheme.Rational.EvenChainCrossSectionStatement
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof

/-! # The split even-path cross-section of the canonical class quotient -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitPinning

open Langlands.LinearAlgebra.RootDatumPathWeights Langlands.LinearAlgebra.PathCoxeter

local instance evenChainCrossSectionIsAffineHom {k F : Type u} [Field k] [Field F] [Algebra k F]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k F)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k F))
  infer_instance

section FieldExtension

variable {k F : Type u} [Field k] [Field F] [Algebra k F] [Algebra.IsAlgebraic k F]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] {p : SplitPinning G}

/-- The ordinary ordered product with canonical representatives at rational coordinates
commutes with the field extension. -/
theorem baseChangeBasePoint_rationalProduct {r : ℕ} (E : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations) (cf : Fin r → k) :
    baseChangeBasePoint (algebraBaseMap k F) G (List.ofFn fun j =>
        (x (E j)).toRootParametrization.rationalPoint (cf j) *
          (canonicalSimpleReflectionRepresentatives x (E j)).point).prod =
      (List.ofFn fun j =>
        (fieldBaseChangeRootMaps (F := F) x
            (fieldBaseChangeOrder (F := F) E j)).toRootParametrization.rationalPoint
            (algebraMap k F (cf j)) *
          (canonicalSimpleReflectionRepresentatives (fieldBaseChangeRootMaps (F := F) x)
            (fieldBaseChangeOrder (F := F) E j)).point).prod := by
  rw [← steinbergProductPoint_rational E x (canonicalSimpleReflectionRepresentatives x) cf,
    baseChangeBasePoint_steinbergProductPoint,
    steinbergProductPoint_rational (fieldBaseChangeOrder (F := F) E)
      (fieldBaseChangeRootMaps (F := F) x)
      (canonicalSimpleReflectionRepresentatives (fieldBaseChangeRootMaps (F := F) x))
      (fun j => algebraMap k F (cf j))]

variable {J : Type u} (C : p.EvenChainData J)

/-- The unmerged coordinates along a path commute with the field extension. -/
theorem EvenChainData.restCoord_fieldBaseChange {q : ℕ} (e : Fin q ≃ C.Rest) (z : Fin q → k)
    (c : J) (v : ℕ) :
    (C.fieldBaseChange (F := F)).restCoord (e.trans (C.restFieldBaseChange (F := F)))
        (fun j => algebraMap k F (z j)) c v = algebraMap k F (C.restCoord e z c v) := by
  classical
  unfold EvenChainData.restCoord
  by_cases hv : v < 2 * C.half c
  · rw [dite_eq_left (show v < 2 * (C.fieldBaseChange (F := F)).half c from hv),
      dite_eq_left hv]
    have hiff : (∀ c', (C.fieldBaseChange (F := F)).path c ⟨v, hv⟩ ≠
          ((C.fieldBaseChange (F := F)).modified c').a ∧
        (C.fieldBaseChange (F := F)).path c ⟨v, hv⟩ ≠
          ((C.fieldBaseChange (F := F)).modified c').b) ↔
        ∀ c', C.path c ⟨v, hv⟩ ≠ (C.modified c').a ∧ C.path c ⟨v, hv⟩ ≠ (C.modified c').b := by
      change (∀ c', p.baseChangeSimpleEquiv (F := F) (C.path c ⟨v, hv⟩) ≠
            p.baseChangeSimpleEquiv (F := F) (C.modified c').a ∧
          p.baseChangeSimpleEquiv (F := F) (C.path c ⟨v, hv⟩) ≠
            p.baseChangeSimpleEquiv (F := F) (C.modified c').b) ↔ _
      simp only [ne_eq, (p.baseChangeSimpleEquiv (F := F)).injective.eq_iff]
    by_cases h' : ∀ c', C.path c ⟨v, hv⟩ ≠ (C.modified c').a ∧
        C.path c ⟨v, hv⟩ ≠ (C.modified c').b
    · rw [dite_eq_left (hiff.mpr h'), dite_eq_left h', Equiv.symm_trans_apply]
      congr 3
    · rw [dite_eq_right (mt hiff.mp h'), dite_eq_right h', map_zero]
  · rw [dite_eq_right (show ¬v < 2 * (C.fieldBaseChange (F := F)).half c from hv),
      dite_eq_right hv, map_zero]

/-- Let a pattern product and an ordinary product along `E` have the same image in the
canonical quotient over `k`. Over the extension `F`, let `Fr` be a fundamental representation at
the end vertex of the path `c`, with constants `A'`, `B'` describing the characteristic
polynomials of the pattern products as in `charpoly_patternProduct`. Then along the path `c` the
extended coordinates of the ordinary product are the pattern coordinates `patCoord`. -/
theorem EvenChainData.patCoord_eq_of_rho_eq (x : p.NormalizedSimpleRootParametrizations)
    {r q N : ℕ} (o : Fin r ≃ J) (e : Fin q ≃ C.Rest) (E : Fin N ≃ p.base.support) (c : J)
    {m : ℕ} (hm : C.half c = m + 1)
    (Fr : (p.baseChange (F := F)).FundamentalRepresentation
      ((C.fieldBaseChange (F := F)).path c
        ⟨0, ((C.fieldBaseChange (F := F)).isPathComponent c).pos⟩))
    {A' B' : F}
    (hAB : ∀ {r q : ℕ} (o : Fin r ≃ J) (e : Fin q ≃ (C.fieldBaseChange (F := F)).Rest)
      (ε : J → Bool) (s : J → F) (t : J → Fˣ) (z : Fin q → F),
      (Fr.representation.rationalMatrix ((C.fieldBaseChange (F := F)).patternProduct
          (fieldBaseChangeRootMaps (F := F) x)
          (canonicalSimpleReflectionRepresentatives (fieldBaseChangeRootMaps (F := F) x))
          o e ε s t z) : Matrix (Fin Fr.dimension) (Fin Fr.dimension) F).charpoly =
        ordPoly m (patCoord m ((C.fieldBaseChange (F := F)).restCoord e z c)
          (if ε c then -((t c : F) * s c * A') else -(s c * A'))
          (if ε c then (t c : F) * B' else 0)))
    (ε : J → Bool) (s : J → k) (t : J → kˣ) (z : Fin q → k) (cf : Fin N → k)
    (h : C.patternProduct x (canonicalSimpleReflectionRepresentatives x) o e ε s t z ≫
        ClassFunctions.rho G = steinbergClassMap E x (canonicalSimpleReflectionRepresentatives x) cf)
    (v : ℕ) (hv : v < 2 * C.half c) :
    patCoord m (fun i => algebraMap k F (C.restCoord e z c i))
        (crossSigma A' (ε c) (algebraMap k F (s c))
          (Units.map (algebraMap k F).toMonoidHom (t c)))
        (crossDelta B' (ε c) (Units.map (algebraMap k F).toMonoidHom (t c))) v =
      algebraMap k F (cf (E.symm (C.path c ⟨v, hv⟩))) := by
  unfold steinbergClassMap at h
  have hF := baseChangeBasePoint_rho_eq_of_rho_eq (F := F) h
  rw [C.baseChangeBasePoint_patternProduct x o e, baseChangeBasePoint_rationalProduct] at hF
  have hch := charpoly_rationalMatrix_eq_of_rho_eq Fr.representation hF
  obtain ⟨v₀, hv₀⟩ := FundamentalRepresentation.exists_pathWeightSpace_ne_zero
    ((C.fieldBaseChange (F := F)).isPathComponent c) Fr
  have h1 := (C.fieldBaseChange (F := F)).patCoord_eq_of_charpoly_eq
    (e.trans (C.restFieldBaseChange (F := F))) (fieldBaseChangeRootMaps (F := F) x) c hm
    Fr.isHighestWeight (Fr.isPathFundamental ((C.fieldBaseChange (F := F)).isPathComponent c))
    v₀ hv₀ hAB o (fieldBaseChangeOrder (F := F) E) ε _ _ _ _ hch v hv
  have hrc : (C.fieldBaseChange (F := F)).restCoord (e.trans (C.restFieldBaseChange (F := F)))
      (fun j => algebraMap k F (z j)) c = fun i => algebraMap k F (C.restCoord e z c i) :=
    funext fun i => C.restCoord_fieldBaseChange e z c i
  rw [hrc] at h1
  refine h1.trans ?_
  change algebraMap k F (cf ((E.trans (p.baseChangeSimpleEquiv (F := F))).symm
    (p.baseChangeSimpleEquiv (F := F) (C.path c ⟨v, hv⟩)))) = _
  rw [Equiv.symm_trans_apply, Equiv.symm_apply_apply]

end FieldExtension

section Assembly

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G} {J : Type u} (C : p.EvenChainData J)

/-- **Cross-section constants.** For a simply connected group there are nonzero constants
`A c`, `B c` in `k` such that every pattern product has the same image in the canonical
quotient as the ordinary product along `mergedFirstOrder e` whose coordinates are the
cross-section coordinates `crossFun e A B ε s t z`. -/
theorem EvenChainData.exists_crossConstants (F : Type u) [Field F] [Algebra k F]
    [Algebra.IsAlgebraic k F] [IsAlgClosed F] (hG : IsSimplyConnected G)
    (x : p.NormalizedSimpleRootParametrizations) {r q : ℕ} (o : Fin r ≃ J)
    (e : Fin q ≃ C.Rest) :
    ∃ A B : J → k, (∀ c, A c ≠ 0) ∧ (∀ c, B c ≠ 0) ∧
      ∀ (ε : J → Bool) (s : J → k) (t : J → kˣ) (z : Fin q → k),
        C.patternProduct x (canonicalSimpleReflectionRepresentatives x) o e ε s t z ≫
            ClassFunctions.rho G =
          steinbergClassMap (C.mergedFirstOrder e) x (canonicalSimpleReflectionRepresentatives x)
            (fun j => C.crossFun e A B ε s t z (C.mergedFirstOrder e j)) := by
  classical
  have hΦ := bijective_steinbergClassMap hG (C.mergedFirstOrder e) x
    (canonicalSimpleReflectionRepresentatives x)
  have hsurj : ∀ (b : Bool) (s0 : k), ∃ g : Fin (C.mergedCount + q) → k,
      C.patternProduct x (canonicalSimpleReflectionRepresentatives x) o e (fun _ => b)
          (fun _ => s0) (fun _ => 1) (fun _ => 0) ≫ ClassFunctions.rho G =
        steinbergClassMap (C.mergedFirstOrder e) x (canonicalSimpleReflectionRepresentatives x) g :=
    fun b s0 => (hΦ.2 _).imp fun _ hg => hg.symm
  choose gam hgam using hsurj
  have hlt : ∀ c, C.half c - 1 < 2 * C.half c := fun c => by have := C.half_pos c; omega
  have hlt' : ∀ c, C.half c - 1 + 1 < 2 * C.half c := fun c => by have := C.half_pos c; omega
  obtain ⟨A, hAdef⟩ : ∃ A : J → k, ∀ c, A c =
      gam false 0 ((C.mergedFirstOrder e).symm (C.path c ⟨C.half c - 1, hlt c⟩)) -
        gam false 1 ((C.mergedFirstOrder e).symm (C.path c ⟨C.half c - 1, hlt c⟩)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : J → k, ∀ c, B c =
      gam true 0 ((C.mergedFirstOrder e).symm (C.path c ⟨C.half c - 1 + 1, hlt' c⟩)) -
        gam false 0 ((C.mergedFirstOrder e).symm (C.path c ⟨C.half c - 1 + 1, hlt' c⟩)) :=
    ⟨_, fun _ => rfl⟩
  have hGK : IsSimplyConnected ((GroupScheme.baseChange (algebraBaseMap k F)).obj G) :=
    isSimplyConnectedFieldExtension k F G hG
  -- The constants of `charpoly_patternProduct` over `F` are the images of `A c` and `B c`.
  have hconst : ∀ (c : J) (Fr : (p.baseChange (F := F)).FundamentalRepresentation
      ((C.fieldBaseChange (F := F)).path c
        ⟨0, ((C.fieldBaseChange (F := F)).isPathComponent c).pos⟩)) {A' B' : F},
      (∀ {r q : ℕ} (o : Fin r ≃ J) (e : Fin q ≃ (C.fieldBaseChange (F := F)).Rest)
        (ε : J → Bool) (s : J → F) (t : J → Fˣ) (z : Fin q → F),
        (Fr.representation.rationalMatrix ((C.fieldBaseChange (F := F)).patternProduct
            (fieldBaseChangeRootMaps (F := F) x)
            (canonicalSimpleReflectionRepresentatives (fieldBaseChangeRootMaps (F := F) x))
            o e ε s t z) : Matrix (Fin Fr.dimension) (Fin Fr.dimension) F).charpoly =
          ordPoly (C.half c - 1) (patCoord (C.half c - 1)
            ((C.fieldBaseChange (F := F)).restCoord e z c)
            (if ε c then -((t c : F) * s c * A') else -(s c * A'))
            (if ε c then (t c : F) * B' else 0))) →
      A' = algebraMap k F (A c) ∧ B' = algebraMap k F (B c) := by
    intro c Fr A' B' hAB
    have hm : C.half c = C.half c - 1 + 1 := by have := C.half_pos c; omega
    have key := fun (b : Bool) (s0 : k) (v : ℕ) (hv : v < 2 * C.half c) =>
      C.patCoord_eq_of_rho_eq (F := F) x o e (C.mergedFirstOrder e) c hm Fr hAB (fun _ => b) (fun _ => s0)
        (fun _ => 1) (fun _ => 0) (gam b s0) (hgam b s0) v hv
    have h00 := key false 0 _ (hlt c)
    have h01 := key false 1 _ (hlt c)
    have h10 := key true 0 _ (hlt' c)
    have h00' := key false 0 _ (hlt' c)
    rw [patCoord_self _ _ _ _ 0] at h00 h01
    rw [patCoord_succ_self] at h10 h00'
    simp only [crossSigma, crossDelta, Bool.false_eq_true, ↓reduceIte, map_zero, map_one,
      Units.val_one, mul_zero, zero_mul, neg_zero, one_mul,
      add_zero] at h00 h01 h10 h00'
    refine ⟨?_, ?_⟩
    · rw [hAdef, map_sub]
      linear_combination h00 - h01
    · rw [hBdef, map_sub]
      linear_combination h10 - h00'
  -- Constants for one fundamental representation at the end of each path.
  have hex : ∀ c, ∃ (Fr : (p.baseChange (F := F)).FundamentalRepresentation
      ((C.fieldBaseChange (F := F)).path c
        ⟨0, ((C.fieldBaseChange (F := F)).isPathComponent c).pos⟩)) (A' B' : F),
      A' = algebraMap k F (A c) ∧ B' = algebraMap k F (B c) ∧ A' ≠ 0 ∧ B' ≠ 0 := by
    intro c
    obtain ⟨Fr⟩ := splitFundamentalRepresentationsExist F _ (p.baseChange (F := F)) hGK
      ((C.fieldBaseChange (F := F)).path c
        ⟨0, ((C.fieldBaseChange (F := F)).isPathComponent c).pos⟩)
    obtain ⟨v₀, hv₀⟩ := FundamentalRepresentation.exists_pathWeightSpace_ne_zero
      ((C.fieldBaseChange (F := F)).isPathComponent c) Fr
    have hm : (C.fieldBaseChange (F := F)).half c = C.half c - 1 + 1 := by
      have := C.half_pos c
      change C.half c = _
      omega
    obtain ⟨A', B', hA', hB', hAB⟩ := (C.fieldBaseChange (F := F)).charpoly_patternProduct
      (fieldBaseChangeRootMaps (F := F) x) c hm Fr.isHighestWeight
      (Fr.isPathFundamental ((C.fieldBaseChange (F := F)).isPathComponent c)) v₀ hv₀
    obtain ⟨h1, h2⟩ := hconst c Fr hAB
    exact ⟨Fr, A', B', h1, h2, hA', hB'⟩
  have hA : ∀ c, A c ≠ 0 := by
    intro c hc
    obtain ⟨_, A', _, h1, _, hA', _⟩ := hex c
    rw [hc, map_zero] at h1
    exact hA' h1
  have hB : ∀ c, B c ≠ 0 := by
    intro c hc
    obtain ⟨_, _, B', _, h2, _, hB'⟩ := hex c
    rw [hc, map_zero] at h2
    exact hB' h2
  refine ⟨A, B, hA, hB, fun ε s t z => ?_⟩
  unfold steinbergClassMap
  apply rho_eq_of_baseChangeBasePoint_rho_eq (F := F)
  rw [C.baseChangeBasePoint_patternProduct x o e, baseChangeBasePoint_rationalProduct]
  apply (C.fieldBaseChange (F := F)).rho_eq_of_charpoly_eq_of_trace_eq hGK
  · intro c Fr
    obtain ⟨v₀, hv₀⟩ := FundamentalRepresentation.exists_pathWeightSpace_ne_zero
      ((C.fieldBaseChange (F := F)).isPathComponent c) Fr
    have hpos := C.half_pos c
    have hm : (C.fieldBaseChange (F := F)).half c = C.half c - 1 + 1 := by
      change C.half c = _
      omega
    obtain ⟨A', B', -, -, hAB⟩ := (C.fieldBaseChange (F := F)).charpoly_patternProduct
      (fieldBaseChangeRootMaps (F := F) x) c hm Fr.isHighestWeight
      (Fr.isPathFundamental ((C.fieldBaseChange (F := F)).isPathComponent c)) v₀ hv₀
    obtain ⟨rfl, rfl⟩ := hconst c Fr hAB
    rw [hAB, charpoly_rootFactorProduct Fr.isHighestWeight
      ((C.fieldBaseChange (F := F)).isPathComponent c)
      (Fr.isPathFundamental ((C.fieldBaseChange (F := F)).isPathComponent c))
      (fieldBaseChangeRootMaps (F := F) x) v₀ hv₀
      (show 2 * (C.fieldBaseChange (F := F)).half c = 2 * (C.half c - 1) + 2 by
        change 2 * C.half c = _
        omega)]
    apply ordPoly_congr
    intro v hv
    have hv' : v < 2 * C.half c := by omega
    rw [dite_eq_left (show v < 2 * (C.fieldBaseChange (F := F)).half c from hv')]
    change _ = algebraMap k F (C.crossFun e A B ε s t z ((C.mergedFirstOrder e) (((C.mergedFirstOrder e).trans
      (p.baseChangeSimpleEquiv (F := F))).symm
        (p.baseChangeSimpleEquiv (F := F) (C.path c ⟨v, hv'⟩)))))
    rw [Equiv.symm_trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply,
      C.crossFun_path, EvenChainData.pathCoord, patCoord_map]
    have hrc : (C.fieldBaseChange (F := F)).restCoord (e.trans (C.restFieldBaseChange (F := F)))
        (fun j => algebraMap k F (z j)) c = fun i => algebraMap k F (C.restCoord e z c i) :=
      funext fun i => C.restCoord_fieldBaseChange e z c i
    have hσ : (if ε c then -(((Units.map (algebraMap k F).toMonoidHom (t c) : Fˣ) : F) *
          algebraMap k F (s c) * algebraMap k F (A c))
        else -(algebraMap k F (s c) * algebraMap k F (A c))) =
        algebraMap k F (crossSigma (A c) (ε c) (s c) (t c)) := by
      unfold crossSigma
      cases ε c <;> simp
    have hδ : (if ε c then ((Units.map (algebraMap k F).toMonoidHom (t c) : Fˣ) : F) *
          algebraMap k F (B c) else 0) =
        algebraMap k F (crossDelta (B c) (ε c) (t c)) := by
      unfold crossDelta
      cases ε c <;> simp
    rw [hrc, hσ, hδ]
  · intro a ha Fr
    have hlam : ∀ c i, (p.baseChange (F := F)).rootDatum.toLinearMap Fr.highestWeight
        ((p.baseChange (F := F)).rootDatum.coroot ((C.fieldBaseChange (F := F)).path c i)) = 0 := by
      intro c i
      rw [Fr.isFundamentalWeight ((C.fieldBaseChange (F := F)).path c i), ite_eq_right (ha c i)]
    rw [(C.fieldBaseChange (F := F)).rationalMatrix_patternProduct_eq_of_offPath
      (e.trans (C.restFieldBaseChange (F := F))) (fieldBaseChangeRootMaps (F := F) x)
      Fr.isHighestWeight hlam o (fieldBaseChangeOrder (F := F) (C.mergedFirstOrder e)) ?h1 ?h2 _ _ _ _
      (fun j => algebraMap k F (C.crossFun e A B ε s t z ((C.mergedFirstOrder e) j))) ?hcf]
    · intro i
      obtain ⟨c, v, hv⟩ := C.exists_path_eq_mergedFirstOrder_castAdd e i
      exact ⟨c, v, congrArg (p.baseChangeSimpleEquiv (F := F)) hv⟩
    · intro j
      change p.baseChangeSimpleEquiv (F := F) (C.mergedFirstOrder e (Fin.natAdd _ j)) =
        p.baseChangeSimpleEquiv (F := F) (e j : p.base.support)
      rw [C.mergedFirstOrder_natAdd]
    · intro j hj
      rw [C.mergedFirstOrder_natAdd, C.crossFun_of_offPath e A B ε s t z j
        (fun c v hv => hj c v (congrArg (p.baseChangeSimpleEquiv (F := F)) hv))]

end Assembly

end SplitPinning

open SplitPinning in
/-- **The split even-path cross-section** (Steinberg 1965, §9.15–9.19, for the actual canonical
quotient). -/
theorem splitEvenChainCrossSection : SplitEvenChainCrossSectionStatement.{u} := by
  intro k _ G _ p hG x J _ C r q o e _ w
  classical
  obtain ⟨A, B, hA, hB, hkey⟩ := C.exists_crossConstants (AlgebraicClosure k) hG x o e
  have hΦ := bijective_steinbergClassMap hG (C.mergedFirstOrder e) x
    (canonicalSimpleReflectionRepresentatives x)
  obtain ⟨cv, hcv⟩ := hΦ.2 w
  obtain ⟨ε, s, t, z, hz⟩ := C.exists_crossFun_eq e hA hB (fun a => cv ((C.mergedFirstOrder e).symm a))
  have hcf : (fun j => C.crossFun e A B ε s t z (C.mergedFirstOrder e j)) = cv :=
    funext fun j => by rw [hz, Equiv.symm_apply_apply]
  refine ⟨C.patternProduct x (canonicalSimpleReflectionRepresentatives x) o e ε s t z,
    ⟨⟨ε, s, t, z, rfl⟩, ?_⟩, ?_⟩
  · rw [hkey, hcf, hcv]
  · rintro g ⟨⟨ε', s', t', z', rfl⟩, hg⟩
    have h1 : steinbergClassMap (C.mergedFirstOrder e) x
        (canonicalSimpleReflectionRepresentatives x)
        (fun j => C.crossFun e A B ε' s' t' z' (C.mergedFirstOrder e j)) =
      steinbergClassMap (C.mergedFirstOrder e) x (canonicalSimpleReflectionRepresentatives x)
        (fun j => C.crossFun e A B ε s t z (C.mergedFirstOrder e j)) := by
      rw [← hkey, hg, hcf, hcv]
    have h2 := hΦ.1 h1
    have h3 : ∀ a, C.crossFun e A B ε' s' t' z' a = C.crossFun e A B ε s t z a := fun a => by
      simpa using congrFun h2 ((C.mergedFirstOrder e).symm a)
    obtain ⟨hε, hs, ht, hz'⟩ := C.eq_of_crossFun_eq e hA hB h3
    exact C.patternProduct_congr e x o hε hs ht hz'

end Langlands.GroupScheme
