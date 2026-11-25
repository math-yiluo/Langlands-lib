import Langlands.GaloisCohomology.Global.BrauerSequence.HigherDegrees.LocalVanishing
import Langlands.GaloisCohomology.Global.BrauerSequence.HigherDegrees.GlobalInvariant
import Langlands.ClassFieldTheory.Global.FundamentalClassProof
import Langlands.ClassFieldTheory.Global.IdeleClassFundamentalTateInput
import Langlands.Cohomology.Profinite.ClassFormation.TateTheorem

/-!
# Inflation kills cohomology of degree `≥ 3` of idèle classes and of local units

*Idèle classes.* Let `F ⊆ E ⊆ L` be number fields with `E / F` and `L / F` finite Galois and
`[E : F] ∣ [L : E]`. Every class of `Hⁿ⁺²(Gal(E/F), C_E)`, `n ≥ 1`, is the cup product `u ∪ y` of
the global fundamental class `u_{E/F}` with a class `y ∈ Hⁿ(Gal(E/F), ℤ)` (Tate's theorem, from the
Library's `fundamentalClass_subgroupConditions` and `exists_cupH_of_tate`). Inflation is compatible
with cup products (`Langlands.Tate.ordinaryCup_map`) and sends `u_{E/F}` to `[L : E] u_{L/F}`
(the Library's global fundamental classes, `globalFundamentalClassStatement`); since
`[E : F] y = 0`, the inflation of `u ∪ y` to `L` is zero (`relativeIdeleClassInflation_eq_zero_of_dvd`).
This is the finite-level form of `Hʳ(G_K, C) = 0` for `r ≥ 3` (Neukirch–Schmidt–Wingberg (3.1.x)
for class formations; Tate in Cassels–Fröhlich VII §11.4).

*Local units.* The same holds for the units of a finite Galois extension of a completion
(`relativeInflation_adicCompletion_eq_zero_of_dvd`), from `relativeInflationLinear_eq_zero_of_dvd`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Limits NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Local FundamentalClass
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u

noncomputable section

section Global

variable {F E L : Type u} [Field F] [Field E] [Field L] [NumberField F] [NumberField E]
  [NumberField L] [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
  [IsGalois F E] [IsGalois F L]

/-- The identity of `ℤ`, as a coefficient map of inflation. -/
def integralInflationIdentity :
    Rep.res (AlgEquiv.restrictNormalHom E : (L ≃ₐ[F] L) →* (E ≃ₐ[F] E))
      (Rep.trivial Langlands.Tate.IntegralScalar.{u} (E ≃ₐ[F] E) Langlands.Tate.IntegralScalar.{u}) ⟶
        Rep.trivial Langlands.Tate.IntegralScalar.{u} (L ≃ₐ[F] L) Langlands.Tate.IntegralScalar.{u} :=
  Rep.ofHom
    { toLinearMap := LinearMap.id
      isIntertwining' _ := rfl }

/-- A family of global fundamental classes of the Library: generating, compatible with
restriction and with inflation. -/
theorem exists_fundamentalClassFamily :
    ∃ c : ClassFamily.{u}, Generates c ∧ Restriction c ∧ Inflation c := by
  obtain ⟨c, ⟨hgen, hres, hinf, -⟩, -⟩ :=
    globalFundamentalClassStatement.2 brauerInvariantFamily fun p _ => brauerInvariantFamily_spec p
  exact ⟨c, hgen, hres, hinf⟩

/-- **Inflation kills idèle-class cohomology of degree `≥ 3`.** If `[E : F] ∣ [L : E]`, inflation
`Hⁿ⁺²(Gal(E/F), C_E) → Hⁿ⁺²(Gal(L/F), C_L)` is zero for `n ≥ 1`. -/
theorem relativeIdeleClassInflation_eq_zero_of_dvd
    (hdvd : Module.finrank F E ∣ Module.finrank E L) (n : ℕ) [NeZero n]
    (x : relativeIdeleClassCohomology F E (n + 2)) :
    relativeIdeleClassInflation F E L (n + 2) x = 0 := by
  classical
  obtain ⟨c, hgen, hres, hinf⟩ := exists_fundamentalClassFamily.{u}
  have hinfl := (inflation_iff_classes c).1 hinf F E L
  let _ : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _
  have hcond := fundamentalClass_subgroupConditions F E c hgen hres
  obtain ⟨y, -, hxy⟩ := ProfiniteCohomology.GroupCoh.exists_cupH_of_tate
    (relativeIdeleClassRepresentation F E) (c F E)
    (fun S => by
      have := (hcond S).1
      exact ModuleCat.isZero_of_subsingleton _)
    (fun S => by
      rw [← Nat.card_zmultiples, (hcond S).2.2, AddSubgroup.card_top, (hcond S).2.1])
    (fun S z => by
      obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1
        ((hcond S).2.2 ▸ AddSubgroup.mem_top z)
      exact ⟨m, hm.symm⟩) n x
  -- the class as a scalar cup product
  have hx : x = (eqToHom (congrArg (groupCohomology (relativeIdeleClassRepresentation F E))
      (add_comm 2 n))).hom (Langlands.Tate.ordinaryCup
        (Langlands.Tate.scalarPairing (relativeIdeleClassRepresentation F E)) 2 n (c F E) y) := by
    rw [hxy, ProfiniteCohomology.GroupCoh.ordinaryCup_scalarPairing]
    exact ProfiniteCohomology.GroupCoh.map_eqToHom_groupCohomology _ (add_comm 2 n) _
  rw [hx]
  erw [Langlands.Tate.map_degree_transport _ _ (add_comm 2 n)]
  rw [Langlands.Tate.ordinaryCup_map (AlgEquiv.restrictNormalHom E)
    (Langlands.Tate.scalarPairing (relativeIdeleClassRepresentation F E))
    (Langlands.Tate.scalarPairing (relativeIdeleClassRepresentation F L))
    (ideleClassInflationCoefficients F E L) integralInflationIdentity
    (ideleClassInflationCoefficients F E L) (fun a b => map_smul _ b a) 2 n (c F E) y]
  have hinfl' : groupCohomology.map (AlgEquiv.restrictNormalHom E)
      (ideleClassInflationCoefficients F E L) 2 (c F E) = Module.finrank E L • c F L := hinfl
  rw [hinfl', map_nsmul, LinearMap.smul_apply, ← map_nsmul]
  have hy : Module.finrank E L • y = 0 := by
    have h0 := ProfiniteCohomology.card_smul_groupCohomology _ (NeZero.ne n) y
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank] at h0
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, mul_comm, mul_smul, h0, smul_zero]
  rw [← map_nsmul, hy, map_zero, map_zero, map_zero]

end Global

section Local

attribute [local instance] isGalois_adicCompletion FiniteExtension.local_finite

variable {F E L : Type u} [Field F] [Field E] [Field L] [NumberField F] [NumberField E]
  [NumberField L] [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
  [IsGalois F E] [IsGalois F L]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (q : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal] [q.asIdeal.LiesOver w.asIdeal] [q.asIdeal.LiesOver v.asIdeal]

/-- **Inflation kills local cohomology of degree `≥ 3`.** At finite places `q | w | v`, if
`[E_w : F_v] ∣ [L_q : E_w]`, inflation `Hⁿ⁺²(Gal(E_w/F_v), E_wˣ) → Hⁿ⁺²(Gal(L_q/F_v), L_qˣ)` is zero
for `n ≥ 1`. -/
theorem relativeInflation_adicCompletion_eq_zero_of_dvd
    (hdvd : Module.finrank (v.adicCompletion F) (w.adicCompletion E) ∣
      Module.finrank (w.adicCompletion E) (q.adicCompletion L)) (n : ℕ) [NeZero n]
    (y : relativeCohomology (padicField v).Carrier (w.adicCompletion E) (n + 2)) :
    relativeInflation (padicField v).Carrier (w.adicCompletion E) (q.adicCompletion L) (n + 2) y =
      0 := by
  obtain ⟨I, -, hRCF, -, -, hF, -⟩ := localRelativeClassFormation.{u} (residuePrime v)
  exact relativeInflationLinear_eq_zero_of_dvd I hRCF (padicField v) (w.adicCompletion E) hF
    (q.adicCompletion L) hdvd n y

end Local

end

end Langlands.GaloisCohomology
