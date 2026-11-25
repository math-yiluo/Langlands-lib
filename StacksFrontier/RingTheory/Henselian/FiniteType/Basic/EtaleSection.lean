module

import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import StacksFrontier.RingTheory.Artinian.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Henselian étale sections and the quasi-finite locus over the closed point

Preliminaries for the decomposition of a finite type algebra over a henselian local ring:
transport of non-quasi-finiteness along algebra isomorphisms, the product decomposition attached
to an idempotent, finiteness of the quasi-finite primes over the maximal ideal, and sections of
étale algebras over a henselian local ring at a residue point.
-/

@[expose] public section

universe u v

/-- A ring map compatible with the structure maps commutes with evaluation of polynomials. -/
private theorem map_aeval_of_algebraMap_comm {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] (f : A →+* B)
    (hf : ∀ r : R, f (algebraMap R A r) = algebraMap R B r) (x : A) (p : Polynomial R) :
    f (Polynomial.aeval x p) = Polynomial.aeval (f x) p :=
  (Polynomial.aeval_algHom_apply ({ f with commutes' := hf } : A →ₐ[R] B) x p).symm

/-- The lift of the structure map of a localization away from `c` is compatible with the
`R`-algebra structures. -/
private theorem away_lift_algebraMap {R R' K : Type*} [CommRing R] [CommRing R'] [CommRing K]
    [Algebra R R'] [Algebra R K] [Algebra R' K] [IsScalarTower R R' K] (c : R')
    (hcunit : IsUnit (algebraMap R' K c)) (r : R) :
    IsLocalization.Away.lift c hcunit (algebraMap R (Localization.Away c) r) =
      algebraMap R K r := by
  rw [IsScalarTower.algebraMap_apply R R' (Localization.Away c) r, IsLocalization.Away.lift_eq,
    ← IsScalarTower.algebraMap_apply R R' K r]

/-- A henselian root of a standard-étale chart. Let `R` be henselian local, let `R'` be an étale
`R`-algebra with a `κ`-rational point `P` over `𝔪` (residue bijectivity `hres`), and let
`Localization.Away c` be a standard-étale chart at `P` (`c ∉ P`) with presentation
`pres : StandardEtalePresentation R (Localization.Away c)`, given by a monic `f`, an element `g`
and the condition `cond`. Then there is an `a : R` with `pres.HasMap a`, that is,
`aeval a pres.f = 0` and `IsUnit (aeval a pres.g)`, whose image in the residue field of `P` is
the prescribed point `pres.x`.

The argument runs as follows.
* The residue bijectivity `κ ≅ R'/P` of `hres` forces the induced `κ`-algebra map on the closed
  fibre `(κ[x]/(f̄))_ḡ = (Localization.Away c) ⊗_R κ` to land in `κ` itself, producing
  `ā := ψ(x̄) ∈ κ` with `f̄(ā) = 0`, with `f̄'(ā) ≠ 0` because `pres.f'` is a unit in the chart,
  and with `ḡ(ā) ≠ 0` because `pres.g` is a unit in the chart.
* As `f` is monic and `ā` is a simple root of `f̄`, `HenselianLocalRing.TFAE` yields an `a : R`
  with `f.IsRoot a`, hence `aeval a pres.f = 0`, and with `residue R a = ā`.
* From `ḡ(ā) ≠ 0` and `a ≡ ā mod 𝔪` we get `g(a) ∉ 𝔪`, hence `IsUnit (aeval a pres.g)` since
  `R` is local. Together these say `pres.HasMap a`. -/
lemma henselian_etale_standardChart_hasMap
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (R' : Type v) [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
    (P : Ideal R') [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (hres : Function.Bijective
      ⇑(Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P (Algebra.ofId R R')
          Ideal.LiesOver.over))
    (c : R')
    (hcunit : IsUnit ((algebraMap R' P.ResidueField) c))
    (pres : StandardEtalePresentation R (Localization.Away c)) :
    ∃ a : R, pres.HasMap a ∧
      algebraMap R P.ResidueField a
        = IsLocalization.Away.lift c hcunit pres.x := by
  classical
  set K := P.ResidueField with hK
  set φ : R →+* K := algebraMap R K with hφ
  set ψ : Localization.Away c →+* K := IsLocalization.Away.lift c hcunit with hψ
  have hcomm : ∀ p : Polynomial R, ψ (Polynomial.aeval pres.x p) = Polynomial.aeval (ψ
      pres.x) p := map_aeval_of_algebraMap_comm ψ (away_lift_algebraMap c hcunit) _
  set ā : K := ψ pres.x with hā
  -- φ is surjective
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨z, hz⟩ := hres.surjective y
    obtain ⟨w, hw⟩ := Ideal.algebraMap_residueField_surjective (IsLocalRing.maximalIdeal R) z
    refine ⟨w, ?_⟩
    rw [hφ]
    have := AlgHom.commutes
      (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P (Algebra.ofId R R')
          Ideal.LiesOver.over) w
    rw [← this, hw, hz]
  -- φ is a local hom
  have hlocal : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    have hker : φ a = 0 := by
      have : a ∈ RingHom.ker φ := by
        rw [IsLocalRing.ker_eq_maximalIdeal φ hφsurj]; exact hmem
      simpa [RingHom.mem_ker] using this
    rw [hker] at ha
    exact (not_isUnit_zero) ha
  -- the lift g : ResidueField R →+* K
  set g : IsLocalRing.ResidueField R →+* K := IsLocalRing.ResidueField.lift φ with hg
  have hg_residue : g.comp (IsLocalRing.residue R) = φ := by
    rw [hg]
    exact IsLocalRing.ResidueField.lift_comp_residue φ
  have hginj : Function.Injective g := (RingHom.injective g)
  -- g commutes with aeval
  have hgcomm : ∀ (b : IsLocalRing.ResidueField R) (p : Polynomial R),
      g (Polynomial.aeval b p) = Polynomial.aeval (g b) p := fun b p =>
    map_aeval_of_algebraMap_comm (R := R) g (RingHom.congr_fun hg_residue) b p
  -- the facts about pres.x
  have hfx : Polynomial.aeval pres.x pres.f = 0 := pres.hasMap.left
  have hgx : IsUnit (Polynomial.aeval pres.x pres.g) := pres.hasMap.right
  -- evals at ā
  have hāf : Polynomial.aeval ā pres.f = 0 := by
    rw [← hcomm, hfx, map_zero]
  have hāg_ne : Polynomial.aeval ā pres.g ≠ 0 := by
    rw [← hcomm]
    exact (hgx.map ψ).ne_zero
  -- derivative ≠ 0 at ā, using pres.cond
  have hādf : Polynomial.aeval ā (Polynomial.derivative pres.f) ≠ 0 := by
    obtain ⟨p₁, p₂, n, hcond⟩ := pres.cond
    have happ := congrArg (Polynomial.aeval ā) hcond
    simp only [map_add, map_mul, map_pow, hāf, zero_mul, add_zero] at happ
    intro hzero
    rw [hzero, zero_mul] at happ
    exact (pow_ne_zero n hāg_ne) happ.symm
  -- choose b : ResidueField R with g b = ā
  obtain ⟨r, hr⟩ := hφsurj ā
  set b : IsLocalRing.ResidueField R := IsLocalRing.residue R r with hb
  have hgb : g b = ā := by
    rw [hb, ← RingHom.comp_apply, hg_residue, hr]
  -- transfer the three facts to b
  have hb_zero : ∀ p : Polynomial R, Polynomial.aeval b p = 0 ↔ Polynomial.aeval ā p = 0 :=
    fun p => by rw [← map_eq_zero_iff g hginj, hgcomm, hgb]
  have hbf : Polynomial.aeval b pres.f = 0 := (hb_zero _).2 hāf
  have hbdf : Polynomial.aeval b (Polynomial.derivative pres.f) ≠ 0 := mt (hb_zero _).1 hādf
  have hbg : Polynomial.aeval b pres.g ≠ 0 := mt (hb_zero _).1 hāg_ne
  -- Hensel lift via TFAE item [1]
  have hH : HenselianLocalRing R := ‹_›
  have hiff := (HenselianLocalRing.TFAE R).out 1 2
  obtain ⟨a, hroot, hres_a⟩ :=
    hiff.mp hH pres.f pres.monic_f b hbf hbdf
  -- assemble pres.HasMap a ∧ pinning equation
  refine ⟨a, ⟨?_, ?_⟩, ?_⟩
  · -- aeval a pres.f = 0
    have : Polynomial.eval a pres.f = 0 := hroot
    rwa [Polynomial.coe_aeval_eq_eval]
  · -- IsUnit (aeval a pres.g)
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    apply hbg
    have hres_g : IsLocalRing.residue R (Polynomial.aeval a pres.g)
        = Polynomial.aeval b pres.g := by
      rw [← hres_a]
      exact map_aeval_of_algebraMap_comm (IsLocalRing.residue R) (fun _ => rfl) _ _
    rw [← hres_g]
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hmem
  · -- pinning: algebraMap R K a = ψ pres.x = ā
    -- φ a = g (residue R a) = g b = ā
    change φ a = ā
    have hφa : φ a = g b := by
      rw [← hg_residue, RingHom.comp_apply, hres_a]
    rw [hφa, hgb]

/-- Residue compatibility of the standard-étale section. Given a standard-étale chart
`Localization.Away c` at `P` (`c ∉ P`) with presentation `pres`, and a henselian root `a : R`
with `pres.HasMap a` pinned to `P` by `hpin`, the section
`σ = (pres.lift a ha) ∘ pres.equivRing ∘ ℓ : R' →ₐ[R] R` is residue-compatible at `P`, that is,
`∀ r' : R', r' - algebraMap R R' (σ r') ∈ P`.

Both `q ∘ σ` and the residue map `ρ = φ⁻¹ ∘ r` — where `r : R' → R'/P` and `φ : κ ≅ R'/P` comes
from the residue bijectivity — are `R`-algebra maps `R' → R'/P`. They agree on the image of `R`
and on the standard-étale generator, since `σ` sends it to the henselian root `a`, which reduces
mod `𝔪` to the root `ā` defining `P`. As the chart is `R`-generated by that variable, the two
maps coincide, giving `r (r' - algebraMap R R' (σ r')) = 0`, i.e. membership in `P = ker r`.

This is not automatic for an arbitrary section: it is exactly the compatibility of the henselian
root with the chosen point. -/
lemma henselian_etale_section_residue_compat
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
    (P : Ideal R') [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (c : R')
    (hcunit : IsUnit ((algebraMap R' P.ResidueField) c))
    (pres : StandardEtalePresentation R (Localization.Away c))
    (a : R) (ha : pres.HasMap a)
    (hpin : algebraMap R P.ResidueField a
        = IsLocalization.Away.lift c hcunit pres.x) :
    ∀ r' : R', r' - algebraMap R R'
      (((pres.lift a ha).comp
        (pres.equivRing.toAlgHom.comp
          (IsScalarTower.toAlgHom R R' (Localization.Away c)))) r') ∈ P := by
  -- `hpin` pins the henselian root `a` to the prescribed point `P`, namely
  -- `algebraMap R P.ResidueField a = ψ pres.x` with `ψ = IsLocalization.Away.lift c hcunit`.
  -- Without it the statement is false: for `R = ℚ`, `R' = ℚ × ℚ` and `f = X(X-1)` the two roots
  -- `{0, 1}` both satisfy `pres.HasMap a`, and the root selecting `Q ≠ P` gives the second
  -- projection, which is residue-incompatible at `P`.  At the call site in
  -- `henselian_etale_residue_point_section`, `hpin` comes for free from
  -- `henselian_etale_standardChart_hasMap`, since the henselian root reduces mod `𝔪` to the root
  -- `ā = ψ pres.x` defining `P`.
  classical
  set K := P.ResidueField with hK
  set L := Localization.Away c with hL
  -- scalar tower instances (hold by rfl)
  have towerK : IsScalarTower R R' K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have towerL : IsScalarTower R R' L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- ψ : L →+* K, the away lift
  set ψ : L →+* K := IsLocalization.Away.lift c hcunit with hψ
  -- ψ is R-linear
  have hψR : ∀ r : R, ψ (algebraMap R L r) = algebraMap R K r := away_lift_algebraMap c hcunit
  -- ψ on R'
  have hψR' : ∀ r' : R', ψ (algebraMap R' L r') = algebraMap R' K r' :=
    fun r' => IsLocalization.Away.lift_eq c hcunit r'
  -- ψ as an R-algebra hom L →ₐ[R] K
  let ψA : L →ₐ[R] K := { ψ with commutes' := hψR }
  -- Φ_res : pres.Ring →ₐ[R] K
  let Φ_res : pres.Ring →ₐ[R] K := ψA.comp pres.equivRing.symm.toAlgHom
  -- Φ_lift : pres.Ring →ₐ[R] K
  let Φ_lift : pres.Ring →ₐ[R] K := (Algebra.ofId R K).comp (pres.lift a ha)
  -- they agree on X
  have hagreeX : Φ_res pres.X = Φ_lift pres.X := by
    change ψA (pres.equivRing.symm pres.X) = (Algebra.ofId R K) ((pres.lift a ha) pres.X)
    rw [pres.lift_X]
    have hsymm : pres.equivRing.symm pres.X = pres.x := by
      rw [← pres.equivRing_x]; exact pres.equivRing.symm_apply_apply pres.x
    rw [hsymm]
    change ψ pres.x = algebraMap R K a
    rw [← hpin]
  -- so Φ_res = Φ_lift
  have hΦ : Φ_res = Φ_lift := StandardEtalePair.hom_ext hagreeX
  -- now conclude
  intro r'
  rw [← Ideal.algebraMap_residueField_eq_zero]
  set σ := ((pres.lift a ha).comp (pres.equivRing.toAlgHom.comp
    (IsScalarTower.toAlgHom R R' L))) with hσ
  rw [map_sub, sub_eq_zero]
  rw [← IsScalarTower.algebraMap_apply R R' K (σ r')]
  rw [← hψR' r']
  have hℓ : algebraMap R' L r' = (IsScalarTower.toAlgHom R R' L) r' := rfl
  rw [hℓ]
  have hσval : σ r' = (pres.lift a ha) (pres.equivRing ((IsScalarTower.toAlgHom R R' L) r')) := rfl
  rw [hσval]
  set y := pres.equivRing ((IsScalarTower.toAlgHom R R' L) r') with hy
  have hback : pres.equivRing.symm y = (IsScalarTower.toAlgHom R R' L) r' := by
    rw [hy]; exact pres.equivRing.symm_apply_apply _
  have e1 : ψ ((IsScalarTower.toAlgHom R R' L) r') = Φ_res y := by
    change ψ ((IsScalarTower.toAlgHom R R' L) r') = ψA (pres.equivRing.symm y)
    rw [hback]; rfl
  rw [e1, hΦ]
  change Φ_lift y = algebraMap R K ((pres.lift a ha) y)
  rfl

/-- Henselian splitting of a residue-rational étale point — the ring-theoretic content of Stacks
04GG part 11, and the fact that EGA IV 18.5.11 invokes.

Let `R` be henselian local with maximal ideal `𝔪` and residue field `κ = R/𝔪`, let `R'` be an
étale `R`-algebra, and let `P` be a prime of `R'` lying over `𝔪` whose induced residue extension
`κ → R'/P` is an isomorphism, i.e. `P` is a `κ`-rational point of the closed fibre (encoded as
bijectivity of `Ideal.ResidueField.mapₐ … (Algebra.ofId R R')`). Then there is an `R`-algebra
retraction `σ : R' →ₐ[R] R` of the structure map `R → R'`, residue-compatible at `P`, hence
splitting off a direct factor `≅ R`.

Equivalently, over a henselian local ring the functor from finite étale `R`-algebras to finite
étale `κ`-algebras is an equivalence on the connected component carrying the `κ`-point. Note that
polynomial Hensel lifting alone (`HenselianLocalRing.TFAE`) gives idempotent lifting for
*module-finite* algebras, not a section over a residue-rational point of a merely quasi-finite
étale algebra. The proof instead passes to a standard-étale chart at `P`, produces a henselian
root of its presentation with `henselian_etale_standardChart_hasMap`, and reads off the section;
residue compatibility is `henselian_etale_section_residue_compat`. -/
lemma henselian_etale_residue_point_section
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
    (P : Ideal R') [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (hres : Function.Bijective
      ⇑(Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P (Algebra.ofId R R')
          Ideal.LiesOver.over)) :
    ∃ σ : R' →ₐ[R] R, ∀ r' : R', r' - algebraMap R R' (σ r') ∈ P := by
  -- A κ-rational point of the closed fibre of an étale R-algebra lifts to a section R' →ₐ[R] R,
  -- and any R-algebra hom R' →ₐ[R] R is automatically a retraction.  Concretely:
  --  * `Algebra.IsEtaleAt.exists_isStandardEtale` gives a standard-étale chart
  --    `Localization.Away c` with `c ∉ P`, and
  --    `IsStandardEtale.nonempty_standardEtalePresentation` gives its presentation `pres`.
  --  * `ℓ := IsScalarTower.toAlgHom R R' (Localization.Away c)` is the localization R-algebra map.
  --  * `φ := pres.equivRing : Localization.Away c ≃ₐ[R] pres.Ring`.
  --  * `henselian_etale_standardChart_hasMap` produces `a : R` with `pres.HasMap a`; then
  --    `τ := pres.lift a ha : pres.Ring →ₐ[R] R`. Compose: `σ := τ ∘ φ ∘ ℓ`.
  obtain ⟨c, hcP, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) (S := R') P
  obtain ⟨pres⟩ := hstd.nonempty_standardEtalePresentation
  let ℓ : R' →ₐ[R] Localization.Away c := IsScalarTower.toAlgHom R R' (Localization.Away c)
  let φ : Localization.Away c ≃ₐ[R] pres.Ring := pres.equivRing
  have hcunit : IsUnit ((algebraMap R' P.ResidueField) c) := by
    rw [isUnit_iff_ne_zero, Ne, Ideal.algebraMap_residueField_eq_zero]; exact hcP
  obtain ⟨a, ha, hpin⟩ := henselian_etale_standardChart_hasMap R R' P hres c hcunit pres
  let τ : pres.Ring →ₐ[R] R := pres.lift a ha
  refine ⟨τ.comp (φ.toAlgHom.comp ℓ), ?_⟩
  -- Residue compatibility of the constructed section: σ realizes the residue isomorphism
  -- R'/P ≅ κ, i.e. q ∘ σ = ρ, the residue map. Both are R-algebra maps R' → R'/P agreeing on the
  -- standard-étale generator — σ sends it to the henselian root a, which reduces mod 𝔪 to the
  -- root ā defining P — hence they agree on all of R'.
  exact henselian_etale_section_residue_compat R R' P c hcunit pres a ha hpin

end
