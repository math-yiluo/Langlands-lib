import Langlands.Weil.Local.ExtensionWeilRangeConjugation
import Langlands.Global.CompletionWeilTransport
import Langlands.ClassField.Global.LocalRelativeWeilMap
import Langlands.LocalFactor.CommonClosure

/-!
# The completion Weil map is conjugate to a transported Weil subgroup

Let `E'/E` be number fields, `u | v` finite places and `f : K ≅ E_v` an isomorphism of
p-adic fields. If `E'_u` is identified with a finite extension `F'` of `K` compatibly with
`f`, and `L` is the extension of `E_v` whose Weil group corresponds to `W_{F'}` under the
transport `W_K ≅ W_{E_v}`, then the image of `W_{E'_u}` in `W_{E_v}` is conjugate to
`W_L` by an element of `W_{E_v}`.
-/

noncomputable section

set_option autoImplicit false

universe u uK

namespace Langlands.Global

open NumberField Langlands.Weil.Local Langlands.Global.CompletionPadic
open Langlands.ClassField.Global Langlands.ClassField.Global.RelativeWeilGroup
open Langlands.LocalFactor.CommonClosure
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

section Base

variable {E : Type u} [Field E] [NumberField E] (v : FinitePlace E)

/-- A finite place whose ideal contains the rational prime `p` has residue
characteristic `p`. -/
theorem residuePrime_eq_of_natCast_mem {p : ℕ} [hp : Fact p.Prime]
    (hv : (p : 𝓞 E) ∈ v.asIdeal) : residuePrime v = p := by
  have h1 : (p : 𝓞 ℚ) ∈ (rationalPlace v).asIdeal := by
    change (p : 𝓞 ℚ) ∈ Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 E)) v.asIdeal
    rw [Ideal.mem_comap, map_natCast]
    exact hv
  have h2 : Rat.HeightOneSpectrum.natGenerator (rationalPlace v) ∣ p := by
    rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
    have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) h1
    rwa [map_natCast] at this
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator _) hp.out).mp h2

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- Two continuous ring homomorphisms `E_v → K` that agree on `E` are equal, since
`E` is dense in `E_v`. -/
theorem completion_ringHom_ext (α β : v.adicCompletion E →+* K.Carrier)
    (hα : letI := K.canonicalTopology; Continuous α)
    (hβ : letI := K.canonicalTopology; Continuous β)
    (hαβ : ∀ x : E, α (algebraMap E _ x) = β (algebraMap E _ x)) : α = β := by
  let := K.canonicalTopology
  have hT := K.canonicalTopologicalData.fieldT2
  rw [PadicField.canonicalTopologicalData_topology] at hT
  have := (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap E v).equalizer hα hβ
    (funext hαβ)
  exact RingHom.ext (congrFun this)

/-- A ring isomorphism `ι : E_v ≅ K` whose inverse is continuous is `ℚ_p`-linear; this is
its inverse as an isomorphism of `ℚ_p`-algebras `K ≅ E_v`. -/
def completionAlgEquivOfContinuous (h : residuePrime v = p)
    (ι : v.adicCompletion E ≃+* K.Carrier)
    (hι : letI := K.canonicalTopology; Continuous ι.symm) :
    letI := (padicFieldAt v h).algebra
    K.Carrier ≃ₐ[Padic p] (padicFieldAt v h).Carrier :=
  letI := (padicFieldAt v h).algebra
  { ι.symm with
    commutes' := fun a => by
      let := K.canonicalTopology
      have hc : Continuous (algebraMap (Padic p) K.Carrier) := continuous_algebraMap _ _
      have hm : Continuous (padicMapAt v h) := by
        subst h
        exact continuous_padicMap v
      have := (Padic.denseRange_ratCast p).equalizer (hι.comp hc) hm
        (funext fun q => by simp only [Function.comp_apply, map_ratCast])
      exact congrFun this a }

@[simp] theorem completionAlgEquivOfContinuous_symm_apply (h : residuePrime v = p)
    (ι : v.adicCompletion E ≃+* K.Carrier)
    (hι : letI := K.canonicalTopology; Continuous ι.symm) (x : v.adicCompletion E) :
    letI := (padicFieldAt v h).algebra
    (completionAlgEquivOfContinuous v K h ι hι).symm x = ι x :=
  rfl

end Base

variable {E : Type u} [Field E] [NumberField E] {E' : Type u} [Field E'] [NumberField E']
  [Algebra E E'] (v : FinitePlace E) (w : FinitePlace E') [w.asIdeal.LiesOver v.asIdeal]
  {p : ℕ} [Fact p.Prime] (h : residuePrime v = p) (K : PadicField.{uK} p)
  (f : letI := (padicFieldAt v h).algebra
    K.Carrier ≃ₐ[Padic p] (padicFieldAt v h).Carrier)

/-- If `E'_w ≅ F'` over `f⁻¹ : E_v ≅ K`, and `W_L` corresponds to `W_{F'}` under the
completion transport, then some `g ∈ W_{E_v}` conjugates the image of `W_{E'_w}` onto
`W_L`. -/
theorem exists_conj_completionWeilMap_range (F' : Extension K)
    (φ : w.adicCompletion E' ≃+* F'.field)
    (hφ : letI := (padicFieldAt v h).algebra
      ∀ x : v.adicCompletion E,
      φ (algebraMap (v.adicCompletion E) (w.adicCompletion E') x) =
        algebraMap K.Carrier F'.field (f.symm x))
    (L : Extension (padicField v))
    (hL : ∀ y : localWeilGroup K,
      completionWeilTransport v h K f y ∈ weilSubgroup (padicField v) L ↔
        y ∈ weilSubgroup K F') :
    ∃ g : localWeilGroup (padicField v), ∀ y : localWeilGroup (padicField v),
      y ∈ (completionWeilMap v w).toMonoidHom.range ↔
        g * y * g⁻¹ ∈ weilSubgroup (padicField v) L := by
  subst h
  let := (padicFieldAt v rfl).algebra
  let c := extensionClosureEquiv (padicFieldAt v rfl) K f.symm.toAlgHom
  let ψ : w.adicCompletion E' →+* AlgebraicClosure (v.adicCompletion E) :=
    c.symm.toRingHom.comp (F'.field.val.toRingHom.comp φ.toRingHom)
  have hcψ (x : w.adicCompletion E') : c (ψ x) = (φ x : AlgebraicClosure K.Carrier) :=
    c.apply_symm_apply _
  have hψ : ∀ x, ψ (completionPadicAlgHom v w x) =
      algebraMap (v.adicCompletion E) (AlgebraicClosure (v.adicCompletion E)) x := by
    intro x
    apply c.injective
    rw [hcψ, completionPadicAlgHom_apply, hφ]
    exact (extensionClosureLift_algebraMap (padicFieldAt v rfl) K f.symm.toAlgHom x).symm
  refine exists_conj_mem_iff_extensionWeilRange (padicField v) (towerPadicField v w)
    (completionPadicAlgHom v w) ψ hψ _ fun y => ?_
  let T := completionWeilTransportEquiv v rfl K f
  obtain ⟨y, rfl⟩ := T.surjective y
  change completionWeilTransport v rfl K f y ∈ _ ↔ _
  rw [hL]
  let σ : Gal(AlgebraicClosure K.Carrier/K.Carrier) := localProjection K y
  refine (IntermediateField.mem_fixingSubgroup_iff F'.field σ).trans ?_
  have key (x : w.adicCompletion E') :
      AlgEquiv.toAlgHom (localProjection (padicField v) (T y)) (ψ x) = ψ x ↔
        σ (φ x : AlgebraicClosure K.Carrier) = φ x := by
    have e1 := extensionClosureLift_galoisMap (padicFieldAt v rfl) K f.symm.toAlgHom σ (ψ x)
    rw [← hcψ x]
    change _ ↔ AlgEquiv.toAlgHom σ (c (ψ x)) = c (ψ x)
    change _ ↔ AlgEquiv.toAlgHom σ
        (extensionClosureLift (padicFieldAt v rfl) K f.symm.toAlgHom (ψ x)) =
      extensionClosureLift (padicFieldAt v rfl) K f.symm.toAlgHom (ψ x)
    rw [← e1]
    exact c.injective.eq_iff.symm
  simp only [key]
  constructor
  · intro hz x
    exact hz _ (φ x).2
  · intro hx z hz
    obtain ⟨x, hx'⟩ := φ.surjective ⟨z, hz⟩
    have := hx x
    rw [hx'] at this
    exact this

end Langlands.Global
