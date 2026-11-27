import Langlands.TraceFormula.GeneralLinearTwistedEllipticCentralizerReduction
import Langlands.TraceFormula.GeneralLinearSimpleTwistedTraceFormulaStatement
import Langlands.TraceFormula.GeneralLinearWeilAdelicTwistProof
import Langlands.TraceFormula.TwistedEllipticClassFinitenessProof
import Langlands.TraceFormula.TwistedClassRepresentatives
import Langlands.Global.AdelicLogSection
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-!
# Rational twisted classes of `Res_{L/K} GL_n` with regular elliptic norm at a finite place

For a cyclic extension `L/K` of number fields with generator `σ`, `W = Res_{L/K} GL_n`, its
Galois twist `Θ` and the ordered norm `N(g) = g Θ(g) ⋯ Θ^{l-1}(g)`, this module proves:

* the component at a finite place `w` of `L` of `N(g)`, read in `GL_n(𝔸_L)`, does not change
  when `g` is multiplied by a point of the positive real torus `A⁺`, since `A⁺` is connected
  and `GL_n(L_w)` is totally disconnected;
* twisted conjugation `g ↦ x⁻¹ g Θ(x)` conjugates `N(g)` by `x`, so regular ellipticity of the
  `w`-component of the norm is a property of the twisted class;
* a compact subset of `W(𝔸_K)¹` on which the `w`-component of the norm is regular elliptic
  meets only finitely many rational twisted classes (from
  `TwistedEllipticClassFinitenessStatement`, proved by `twistedEllipticClassFiniteness`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Topology
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme Langlands.JacquetLanglands Langlands.BaseChange
open Langlands.TraceFormula.AdelicGroupAutomorphism

namespace Langlands.TraceFormula

section Topology

/-- The general linear group over a nonarchimedean completion of a number field is totally
disconnected. -/
theorem totallyDisconnectedSpace_finiteLocalGL (L : Type*) [Field L] [NumberField L]
    (w : Langlands.Global.FinitePlace L) (n : ℕ) :
    TotallyDisconnectedSpace (FiniteLocalGL L n w) := by
  have : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) (FiniteCompletion L w)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → _))
  exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn
    Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

/-- A continuous homomorphism from a connected group to a totally disconnected group is
trivial. -/
theorem apply_eq_one_of_connectedSpace {A B : Type*} [Group A] [TopologicalSpace A]
    [ConnectedSpace A] [Group B] [TopologicalSpace B] [TotallyDisconnectedSpace B]
    (ρ : A →* B) (hρ : Continuous ρ) (a : A) : ρ a = 1 := by
  have h := (isPreconnected_univ.image ρ hρ.continuousOn).subsingleton
  rw [← map_one ρ]
  exact h ⟨a, Set.mem_univ _, rfl⟩ ⟨1, Set.mem_univ _, rfl⟩

/-- The positive real points `A⁺` of a split torus mapping to `G` with injective finite-index
character restriction form a connected group: `positiveAmbientLogEquiv` identifies them with
a real vector space. -/
theorem connectedSpace_intrinsicSubgroup {F : Type u} [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ G) (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex] (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) :
    ConnectedSpace (intrinsicSubgroup F T) := by
  have : PathConnectedSpace (RealCharacterDual F G) := IsTopologicalAddGroup.pathConnectedSpace
  have hM : ConnectedSpace (Multiplicative (RealCharacterDual F G)) :=
    Function.Surjective.connectedSpace (f := Multiplicative.ofAdd)
      Multiplicative.ofAdd.surjective continuous_ofAdd
  exact Function.Surjective.connectedSpace
    (positiveAmbientLogEquiv F G T i hi I e).symm.surjective
    (positiveAmbientLogEquiv F G T i hi I e).symm.continuous

end Topology

section Norm

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}

/-- Twisted conjugation `q ↦ x⁻¹ q Θ(x)` turns the ordered norm
`q Θ(q) ⋯ Θ^{l-1}(q)` into `x⁻¹ (q Θ(q) ⋯ Θ^{l-1}(q)) Θ^l(x)`. -/
theorem adelicNorm_twistedConj (e : Aut G) (l : ℕ) (x q : AdelicGroupPoints F G) :
    ((List.range l).map fun k => adelicAut F (e ^ k) (x⁻¹ * q * adelicAut F e x)).prod =
      x⁻¹ * ((List.range l).map fun k => adelicAut F (e ^ k) q).prod *
        adelicAut F (e ^ l) x := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, List.map_append,
      List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_mul,
      map_inv]
    rw [← adelicAut_mul_apply, ← pow_succ]
    group

end Norm

section GeneralLinear

attribute [local instance] generalLinearSimpleTwistedTraceIsAffine
  generalLinearSimpleTwistedTraceSmooth

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "Wₙ" => weilGroup K L GLₙ

set_option hygiene false in
local notation "τₙ" => unitGaloisAut K L GLₙ σ

set_option hygiene false in
/-- The ordered norm `g Θ(g) ⋯ Θ^{l-1}(g)` on `W(𝔸_K)`. -/
local notation "Nₙ" g:max => ((List.range l).map fun k => adelicAut K (τₙ ^ k) g).prod

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] {σ : L ≃ₐ[K] L} {l n : ℕ}

/-- The `w`-component of the norm, read in `GL_n(𝔸_L)`. -/
local notation "localNormₙ" w:max g:max => FiniteAdelicGL.localProjection L n w
  (AdelicGL.finite L n (cyclicWeilAdelicMap K L n (Nₙ g)))

omit [NumberField K] [NumberField L] in
theorem unitGaloisAut_pow_eq_one (hcyc : IsCyclicAlgebra σ l) : τₙ ^ l = 1 := by
  rw [← unitGaloisAutHom_apply, ← map_pow, hcyc.pow_eq_one, map_one]

/-- The composite `W(𝔸_K) → GL_n(𝔸_L) → GL_n(𝔸_{L,f}) → GL_n(L_w)` is a continuous
homomorphism. -/
theorem exists_weilLocalHom (w : Langlands.Global.FinitePlace L) :
    ∃ ψ : AdelicGroupPoints K Wₙ →* FiniteLocalGL L n w, Continuous ψ ∧
      ∀ g, ψ g = FiniteAdelicGL.localProjection L n w
        (AdelicGL.finite L n (cyclicWeilAdelicMap K L n g)) := by
  obtain ⟨⟨E, hE⟩, -, -⟩ := generalLinearWeilAdelicTwist K L n
  refine ⟨(FiniteAdelicGL.localProjection L n w).toMonoidHom.comp
    ((AdelicGL.finite L n).toMonoidHom.comp E.toMonoidHom),
    (FiniteAdelicGL.localProjection L n w).continuous.comp
      ((AdelicGL.finite L n).continuous.comp E.continuous), fun g => ?_⟩
  change FiniteAdelicGL.localProjection L n w (AdelicGL.finite L n (E g)) = _
  rw [hE]
  rfl

/-- Multiplying by a positive real point does not change the `w`-component of the norm:
each `Θ^k(a)` with `a ∈ A⁺` has trivial `w`-component, as `A⁺` is connected and
`GL_n(L_w)` is totally disconnected. -/
theorem localNorm_positivePointMap_mul (T : CommGroupScheme (Spec (CommRingCat.of K)))
    (i : T.toGrp ⟶ Wₙ) (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex] (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
    (w : Langlands.Global.FinitePlace L) (a : intrinsicSubgroup K T)
    (z : AdelicGroupPoints K Wₙ) :
    (localNormₙ w (positivePointMap K Wₙ T i a * z)) = localNormₙ w z := by
  obtain ⟨ψ, hψc, hψ⟩ := exists_weilLocalHom (K := K) (n := n) w
  have : ConnectedSpace (intrinsicSubgroup K T) :=
    connectedSpace_intrinsicSubgroup Wₙ T i hi I e
  have : TotallyDisconnectedSpace (FiniteLocalGL L n w) :=
    totallyDisconnectedSpace_finiteLocalGL L w n
  have hone : ∀ k : ℕ, ψ (adelicAut K (τₙ ^ k) (positivePointMap K Wₙ T i a)) = 1 := by
    intro k
    let ρ : intrinsicSubgroup K T →* FiniteLocalGL L n w :=
      ψ.comp ((adelicAut K (τₙ ^ k)).toMonoidHom.comp (positivePointMap K Wₙ T i).toMonoidHom)
    exact apply_eq_one_of_connectedSpace ρ
      (hψc.comp ((adelicAut K (τₙ ^ k)).continuous.comp (positivePointMap K Wₙ T i).continuous)) a
  rw [← hψ, ← hψ, map_list_prod, map_list_prod, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_apply, map_mul, hone, one_mul]

/-- Twisted conjugation conjugates the norm, so regular ellipticity of the `w`-component of
the norm depends only on the twisted class. -/
theorem isRegularElliptic_localNorm_twistedConj (hcyc : IsCyclicAlgebra σ l)
    (w : Langlands.Global.FinitePlace L) (x q : AdelicGroupPoints K Wₙ) :
    IsRegularElliptic (localNormₙ w (x⁻¹ * q * adelicAut K τₙ x)) ↔
      IsRegularElliptic (localNormₙ w q) := by
  obtain ⟨ψ, -, hψ⟩ := exists_weilLocalHom (K := K) (n := n) w
  rw [← hψ, ← hψ, adelicNorm_twistedConj, unitGaloisAut_pow_eq_one hcyc, adelicAut_one_apply,
    map_mul, map_mul, map_inv]
  unfold IsRegularElliptic IsRegularSemisimple
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']

set_option maxRecDepth 2000 in
/-- The identification `W(𝔸_K) ≃ GL_n(𝔸_L)` in the form used below: a topological group
isomorphism with underlying map `cyclicWeilAdelicMap`, intertwining the Galois twist with the
entrywise action of `σ`. -/
theorem exists_weilAdelicEquiv :
    ∃ E : AdelicGroupPoints K Wₙ ≃ₜ* AdelicGL L n,
      (∀ g, E g = cyclicWeilAdelicMap K L n g) ∧
      (∀ g, cyclicWeilAdelicMap K L n (adelicAut K τₙ g) =
        AdelicGLTransport.adelicEquiv n (σ : L ≃+* L) (cyclicWeilAdelicMap K L n g)) ∧
      ∀ g, g ∈ AdelicGroupPoints.rationalSubgroup K Wₙ ↔
        cyclicWeilAdelicMap K L n g ∈ (AdelicGL.rational L n).range := by
  obtain ⟨⟨E, hE⟩, htwist, hrat⟩ := generalLinearWeilAdelicTwist K L n
  exact ⟨E, fun g => by rw [hE]; rfl, htwist σ, hrat⟩

/-- A twisted conjugacy `h⁻¹ δ σ(h) = δ'` in `GL_n(L)` between the coordinates of two rational
points of `W(𝔸_K)¹` makes them twisted-conjugate under the rational subgroup. -/
theorem isTwistedConjugate_of_rational_coordinates (q q' : rationalNormOneSubgroup K Wₙ)
    (δ δ' h : GeneralLinear n L)
    (hq : cyclicWeilAdelicMap K L n q.val.val = AdelicGL.rational L n δ)
    (hq' : cyclicWeilAdelicMap K L n q'.val.val = AdelicGL.rational L n δ')
    (hh : h⁻¹ * δ * entrywiseAut σ n h = δ') :
    IsTwistedConjugate (rationalNormOneSubgroup K Wₙ) (normOneAut K τₙ)
      (q : normOneSubgroup K Wₙ) (q' : normOneSubgroup K Wₙ) := by
  obtain ⟨E, hEΦ, htwist, hrat⟩ := exists_weilAdelicEquiv (K := K) (L := L) (σ := σ) (n := n)
  let x : AdelicGroupPoints K Wₙ := E.symm (AdelicGL.rational L n h)
  have hEx : E x = AdelicGL.rational L n h := E.apply_symm_apply _
  have hx : x ∈ AdelicGroupPoints.rationalSubgroup K Wₙ :=
    (hrat x).mpr ⟨h, by rw [← hEΦ, hEx]⟩
  obtain ⟨y, hy⟩ := hx
  have hxN : x ∈ normOneSubgroup K Wₙ := rationalSubgroup_le_normOneSubgroup K Wₙ ⟨y, hy⟩
  refine ⟨⟨x, hxN⟩, ⟨y, Subtype.ext hy⟩, ?_⟩
  apply Subtype.ext
  apply E.injective
  change E (x⁻¹ * q.val.val * adelicAut K τₙ x) = E q'.val.val
  rw [map_mul, map_mul, map_inv, hEx, hEΦ (adelicAut K τₙ x), htwist, ← hEΦ x, hEx,
    hEΦ q.val.val, hEΦ q'.val.val, hq, hq', AdelicGLTransport.adelicEquiv_rational, ← hh,
    map_mul, map_mul, map_inv]
  rfl

set_option maxHeartbeats 800000 in
/-- A compact subset `Ω` of `W(𝔸_K)¹` on which the `w`-component of the norm is regular
elliptic meets finitely many rational twisted classes. There are finitely many rational
points, pairwise not twisted-conjugate and each with regular elliptic norm at `w`, which
represent every rational point twisted-conjugate under `W(𝔸_K)¹` into `Ω`. -/
theorem exists_twistedClass_representatives_of_isCompact (hcyc : IsCyclicAlgebra σ l)
    (w : Langlands.Global.FinitePlace L) (Ω : Set (normOneSubgroup K Wₙ)) (hΩ : IsCompact Ω)
    (hell : ∀ z ∈ Ω, IsRegularElliptic
      (localNormₙ w ((z : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ))) :
    ∃ (m : ℕ) (r : Fin m → rationalNormOneSubgroup K Wₙ),
      (∀ j k, IsTwistedConjugate (rationalNormOneSubgroup K Wₙ) (normOneAut K τₙ)
        (r j : normOneSubgroup K Wₙ) (r k : normOneSubgroup K Wₙ) → j = k) ∧
      (∀ j, IsRegularElliptic
        (localNormₙ w ((r j : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ))) ∧
      ∀ q ∈ rationalNormOneSubgroup K Wₙ,
        (∃ x : normOneSubgroup K Wₙ, x⁻¹ * q * normOneAut K τₙ x ∈ Ω) →
        ∃ j, IsTwistedConjugate (rationalNormOneSubgroup K Wₙ) (normOneAut K τₙ)
          (r j : normOneSubgroup K Wₙ) q := by
  classical
  obtain ⟨E, hEΦ, htwist, -⟩ := exists_weilAdelicEquiv (K := K) (L := L) (σ := σ) (n := n)
  let Γ := rationalNormOneSubgroup K Wₙ
  let θ := normOneAut K τₙ
  let S : Set Γ := {q | ∃ x : normOneSubgroup K Wₙ, x⁻¹ * (q : normOneSubgroup K Wₙ) * θ x ∈ Ω}
  have hellS : ∀ q ∈ S, IsRegularElliptic
      (localNormₙ w ((q : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ)) := by
    rintro q ⟨x, hx⟩
    have h := hell _ hx
    change IsRegularElliptic (localNormₙ w ((x : AdelicGroupPoints K Wₙ)⁻¹ *
      ((q : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ) *
        adelicAut K τₙ (x : AdelicGroupPoints K Wₙ))) at h
    exact (isRegularElliptic_localNorm_twistedConj hcyc w _ _).mp h
  have hΦc : Continuous (cyclicWeilAdelicMap K L n) := by
    have h : (cyclicWeilAdelicMap K L n) = E := funext fun g => (hEΦ g).symm
    rw [h]
    exact E.continuous
  let Ωa : Set (AdelicGL L n) :=
    cyclicWeilAdelicMap K L n '' (Subtype.val '' Ω)
  have hΩa : IsCompact Ωa := (hΩ.image continuous_subtype_val).image hΦc
  obtain ⟨R, -, hR⟩ := twistedEllipticClassFiniteness K L σ l hcyc n Ωa hΩa
  have key : ∀ q ∈ S, ∃ ρ ∈ R, ∃ δ y : GeneralLinear n L,
      cyclicWeilAdelicMap K L n ((q : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ) =
        AdelicGL.rational L n δ ∧ y⁻¹ * δ * entrywiseAut σ n y = ρ := by
    intro q hq
    obtain ⟨δ, hqδ, hδ⟩ := exists_sigmaElliptic_rational_matrix_of_isRegularElliptic_localNorm
      generalLinearWeilAdelicTwist hcyc q w (hellS q hq)
    obtain ⟨x, hx⟩ := hq
    have hmeets : ∃ x' : AdelicGL L n,
        x'⁻¹ * AdelicGL.rational L n δ * AdelicGLTransport.adelicEquiv n (σ : L ≃+* L) x' ∈
          Ωa := by
      refine ⟨cyclicWeilAdelicMap K L n x.val, _, ⟨_, hx, rfl⟩, ?_⟩
      change cyclicWeilAdelicMap K L n ((x : AdelicGroupPoints K Wₙ)⁻¹ *
        ((q : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ) *
          adelicAut K τₙ (x : AdelicGroupPoints K Wₙ)) = _
      rw [← hEΦ, map_mul, map_mul, map_inv, hEΦ, hEΦ, hEΦ, htwist, hqδ]
    obtain ⟨ρ, hρ, y, hy⟩ := hR δ hδ hmeets
    exact ⟨ρ, hρ, δ, y, hqδ, hy⟩
  choose! ρ hρR δ y hqδ hy using key
  obtain ⟨m, r, hrS, hpair, hcover⟩ := exists_twistedClass_representatives Γ θ S ρ
    (R : Set (GeneralLinear n L)) R.finite_toSet hρR (by
      intro q hq q' hq' hqq'
      refine isTwistedConjugate_of_rational_coordinates q q' (δ q) (δ q')
        (y q * (y q')⁻¹) (hqδ q hq) (hqδ q' hq') ?_
      have e1 := hy q hq
      have e2 := hy q' hq'
      rw [hqq'] at e1
      calc (y q * (y q')⁻¹)⁻¹ * δ q * entrywiseAut σ n (y q * (y q')⁻¹)
          = y q' * ((y q)⁻¹ * δ q * entrywiseAut σ n (y q)) *
              (entrywiseAut σ n (y q'))⁻¹ := by
            rw [map_mul, map_inv]
            group
        _ = δ q' := by
            rw [e1, ← e2]
            group)
  refine ⟨m, r, hpair, fun j => hellS _ (hrS j), ?_⟩
  intro q hq hx
  exact hcover ⟨q, hq⟩ hx

end GeneralLinear

end Langlands.TraceFormula
