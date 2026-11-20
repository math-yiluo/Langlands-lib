import Langlands.GroupScheme.Rational.CentralNormOneArchimedeanCorrection
import Langlands.GroupScheme.Rational.CentralSplitTorsionCocycleLift

/-! # Simultaneous archimedean correction through split torsion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField groupCohomology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IsCentralIsogeny

open GaloisPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F I : Type u} [Field F] [Finite I]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H}
  (hf : IsCentralIsogeny f) (n : I → ℕ) (e : kernel f ≅ splitRootsOfUnityProduct F n)

local notation "χ" i => splitRootsKernelCharacter n e i

section Global

variable {E : Type u} [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

/-- A family of Kummer radicals on one Galois cover gives a natural cocycle of
the actual split torsion kernel. -/
def splitRootsKummerKernelCocycle (a : I → Fˣ) {z : I → Eˣ}
    (hz : ∀ i, z i ^ n i = Units.map (algebraMap F E) (a i)) :
    Cocycle (kernel f) (GaloisCocycle.cover F E) := by
  let d (σ : Gal(E/F)) : GaloisCocycle.cover F E ⟶ (kernel f).X :=
    (hf.kernelSplitRootsEquiv n e E).symm
      (fun i => KummerCocycle.rootValue (n i) (a i) (hz i) σ)
  have hd (i : I) (σ : Gal(E/F)) :
      hf.kernelUnitMap (χ i) E (d σ) = KummerCocycle.value (z i) σ :=
    hf.kernelUnitMap_splitRoots_symm n e E _ i
  refine GaloisCocycle.ofValues d (fun σ τ =>
    hf.kernelUnitMap_splitRoots_jointly_injective n e E (fun i => ?_))
  have hσ : hf.kernelUnitMap (χ i) E (GaloisPoint.conjugate F E (kernel f) σ (d τ)) =
      σ • hf.kernelUnitMap (χ i) E (d τ) :=
    hf.kernelUnitMap_naturality (χ i) σ.toAlgHom (d τ)
  rw [map_mul, hσ, hd, hd, hd, mul_comm]
  exact KummerCocycle.value_isMulCocycle (z i) σ τ

theorem kernelUnitMap_value_splitRootsKummerKernelCocycle (a : I → Fˣ) {z : I → Eˣ}
    (hz : ∀ i, z i ^ n i = Units.map (algebraMap F E) (a i)) (i : I) (σ : Gal(E/F)) :
    hf.kernelUnitMap (χ i) E (GaloisCocycle.value (hf.splitRootsKummerKernelCocycle n e a hz) σ) =
      KummerCocycle.value (z i) σ := by
  unfold splitRootsKummerKernelCocycle
  rw [GaloisCocycle.value_ofValues]
  exact hf.kernelUnitMap_splitRoots_symm n e E _ i

end Global

section Local

variable {K L M : Type u} [Field K] [Field L] [Field M]
  [Algebra F K] [Algebra F L] [Algebra F M] [Algebra K M] [Algebra L M]
  [IsScalarTower F K M] [IsScalarTower F L M] [Normal F L]

/-- Kummer data for the coordinates of a local correction in a split torsion kernel. -/
structure LocalSplitRootsCorrection (ζ : Cocycle G (GaloisCocycle.cover F L)) where
  coeff : hf.LocalCentralCorrection (K := K) (M := M) ζ
  scalar : I → Kˣ
  radical : I → Mˣ
  radical_pow : ∀ i, radical i ^ n i = Units.map (algebraMap K M) (scalar i)
  unit_eq : ∀ (i : I) (σ : Gal(M/K)),
    hf.kernelUnitMap (χ i) M (coeff.correction σ) = KummerCocycle.value (radical i) σ

theorem nonempty_localSplitRootsCorrection [IsAlgClosed M] [FiniteDimensional K M] [IsGalois K M]
    (ζ : Cocycle G (GaloisCocycle.cover F L))
    (h : ((ζ.map f).baseChangePullback (Spec.algebraMap F K)).IsTrivial) :
    Nonempty (hf.LocalSplitRootsCorrection (K := K) (M := M) n e ζ) := by
  obtain ⟨d⟩ := hf.nonempty_localCentralCorrection (K := K) (M := M) ζ h
  let c (i : I) (σ : Gal(M/K)) := hf.kernelUnitMap (χ i) M (d.correction σ)
  have hc (i : I) : IsMulCocycle₁ (c i) := by
    intro σ τ
    have hσ : hf.kernelUnitMap (χ i) M
        (relativeConjugate F K M hf.commutativeKernel.toGrp σ (d.correction τ)) = σ • c i τ :=
      hf.kernelUnitMap_naturality (χ i) (σ.restrictScalars F).toAlgHom (d.correction τ)
    change hf.kernelUnitMap (χ i) M (d.correction (σ * τ)) = σ • c i τ * c i σ
    rw [d.correction_mul, map_mul, hσ, mul_comm]
  have hp (i : I) (σ : Gal(M/K)) : c i σ ^ n i = 1 := by
    change hf.kernelUnitMap (χ i) M (d.correction σ) ^ n i = 1
    rw [← hf.kernelSplitRootsEquiv_val n e]
    exact (mem_rootsOfUnity (n i) _).mp (hf.kernelSplitRootsEquiv n e M (d.correction σ) i).property
  have hrad (i : I) : ∃ (a : Kˣ) (z : Mˣ), z ^ n i = Units.map (algebraMap K M) a ∧
      ∀ σ : Gal(M/K), KummerCocycle.value z σ = c i σ :=
    KummerCocycle.exists_radical (n i) (c i) (hc i) (hp i)
  choose a z hpow hz using hrad
  exact ⟨⟨d, a, z, hpow, fun i σ => (hz i σ).symm⟩⟩

variable {E : Type u} [Field E] [Algebra F E] [Algebra L E] [Algebra E M]
  [IsScalarTower F L E] [IsScalarTower F E M] [IsScalarTower L E M]
  [FiniteDimensional F E] [IsGalois F E] [FiniteDimensional K M] [IsGalois K M]

set_option maxHeartbeats 650000 in
/-- Matching power classes in every coordinate give a single local trivialization. -/
theorem LocalSplitRootsCorrection.isTrivial_of_powerClasses
    {ζ : Cocycle G (GaloisCocycle.cover F L)}
    (d : hf.LocalSplitRootsCorrection (K := K) (M := M) n e ζ)
    (a : I → Fˣ) {z : I → Eˣ} (hz : ∀ i, z i ^ n i = Units.map (algebraMap F E) (a i))
    (q : I → Kˣ) (hq : ∀ i, Units.map (algebraMap F K).toMonoidHom (a i) = d.scalar i * q i ^ n i) :
    (((ζ.refine (GaloisCocycle.coverMap F L E)).divCentral
      (hf.splitRootsKummerKernelCocycle n e a hz) (kernelι f) hf.isCentral_kernelι).baseChangePullback
        (Spec.algebraMap F K)).IsTrivial := by
  let α := hf.splitRootsKummerKernelCocycle n e a hz
  let z₀ (i : I) : Mˣ := Units.map (algebraMap E M) (z i)
  have hz₀ (i : I) : z₀ i ^ n i =
      Units.map (algebraMap K M).toMonoidHom (Units.map (algebraMap F K).toMonoidHom (a i)) := by
    simp only [z₀, ← map_pow, hz]
    apply Units.ext
    change algebraMap E M (algebraMap F E (a i : F)) = algebraMap K M (algebraMap F K (a i : F))
    rw [← IsScalarTower.algebraMap_apply F E M, ← IsScalarTower.algebraMap_apply F K M]
  have ht (i : I) : ∃ t : rootsOfUnity (n i) M, ∀ σ : Gal(M/K),
      KummerCocycle.value (z₀ i) σ / KummerCocycle.value (d.radical i) σ =
        KummerCocycle.value (t : Mˣ) σ :=
    KummerCocycle.exists_root_compare (n i) (Units.map (algebraMap F K).toMonoidHom (a i)) (d.scalar i)
      (q i) (hz₀ i) (d.radical_pow i) (hq i)
  choose t ht using ht
  let T := (hf.kernelSplitRootsEquiv n e M).symm t
  apply LocalCentralCorrection.isTrivial_of_coboundaryRatio hf d.coeff α T
  intro σ
  apply hf.kernelUnitMap_splitRoots_jointly_injective n e M
  intro i
  let ρ := (σ.restrictScalars F).restrictNormal E
  let D := relativeExtend F E M hf.commutativeKernel.toGrp (GaloisCocycle.value α ρ)
  let u := hf.kernelUnitMap (χ i) M
  have hD : u D = KummerCocycle.value (z₀ i) σ := by
    change hf.kernelUnitMap (χ i) M
      (GroupScheme.affinePointMap hf.commutativeKernel.toGrp
        (CommAlgCat.ofHom (IsScalarTower.toAlgHom F E M)) (GaloisCocycle.value α ρ)) = _
    rw [hf.kernelUnitMap_naturality (χ i) (IsScalarTower.toAlgHom F E M),
      hf.kernelUnitMap_value_splitRootsKummerKernelCocycle n e a hz]
    simp only [KummerCocycle.value, z₀, map_div]
    congr 1
    apply Units.ext
    exact ((σ.restrictScalars F).restrictNormal_commutes E (z i : E))
  change u (D / d.coeff.correction σ) =
    u (relativeConjugate F K M hf.commutativeKernel.toGrp σ T / T)
  have hσ : u (relativeConjugate F K M hf.commutativeKernel.toGrp σ T) = σ • u T :=
    hf.kernelUnitMap_naturality (χ i) (σ.restrictScalars F).toAlgHom T
  have hu : u T = (t i).val := hf.kernelUnitMap_splitRoots_symm n e M t i
  rw [map_div, map_div, hD, show u (d.coeff.correction σ) = _ from d.unit_eq i σ, hσ, hu]
  exact ht i σ

end Local

variable {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L] [NumberField F]

include e in
set_option maxHeartbeats 850000 in
/-- A projected archimedean-trivial cocycle has one simultaneous central correction
for any finite split product of positive-exponent roots-of-unity groups. -/
theorem hasArchimedeanCentralCorrection_of_splitRootsKernel
    (hn : ∀ i, 0 < n i) (ζ : Cocycle G (GaloisCocycle.cover F L)) (h : (ζ.map f).ArchimedeanTrivial) :
    hf.HasArchimedeanCentralCorrection ζ := by
  let K (v : InfinitePlace F) := v.Completion
  let M (v : InfinitePlace F) := AlgebraicClosure (K v)
  let : ∀ v : InfinitePlace F, FiniteDimensional (K v) (M v) :=
    fun v => Global.finiteArchimedeanAlgebraicClosure F v
  let : ∀ v : InfinitePlace F, CharZero (K v) :=
    fun v => charZero_of_injective_algebraMap (algebraMap F (K v)).injective
  let : ∀ v : InfinitePlace F, IsGalois (K v) (M v) :=
    fun _ => isGalois_iff.mpr ⟨inferInstance, ⟨fun _ => IsAlgClosed.splits _⟩⟩
  let jL (v : InfinitePlace F) : L →ₐ[F] M v := IsAlgClosed.lift
  let : ∀ v : InfinitePlace F, Algebra L (M v) := fun v => (jL v).toRingHom.toAlgebra
  let : ∀ v : InfinitePlace F, IsScalarTower F L (M v) :=
    fun v => IsScalarTower.of_algebraMap_eq fun x => ((jL v).commutes x).symm
  let d (v : InfinitePlace F) :=
    Classical.choice (hf.nonempty_localSplitRootsCorrection (K := K v) (M := M v) n e ζ (h v))
  have happrox (i : I) : ∃ a : Fˣ,
      Global.RepresentsArchimedeanUnitPowers F (n i) a (fun v => (d v).scalar i) :=
    Global.exists_representsArchimedeanUnitPowers F (hn i) (fun v => (d v).scalar i)
  choose a ha using happrox
  obtain ⟨E, _, _, _, _, _, _, z, hz⟩ := exists_finiteGalois_unit_roots_family (F := F) n hn
    (fun i => Units.map (algebraMap F L).toMonoidHom (a i))
  let : FiniteDimensional L E := FiniteDimensional.right F L E
  have hz' (i : I) : z i ^ n i = Units.map (algebraMap F E) (a i) := by
    rw [hz]
    apply Units.ext
    exact (IsScalarTower.algebraMap_apply F L E (a i : F)).symm
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hf.splitRootsKummerKernelCocycle n e a hz', ?_⟩
  intro v
  let jE : E →ₐ[L] M v := IsAlgClosed.lift
  let : Algebra E (M v) := jE.toRingHom.toAlgebra
  let : IsScalarTower L E (M v) := IsScalarTower.of_algebraMap_eq fun x => (jE.commutes x).symm
  let : IsScalarTower F E (M v) := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply F L E, ← IsScalarTower.algebraMap_apply L E (M v),
      IsScalarTower.algebraMap_apply F L (M v)]
  have hq (i : I) : ∃ q : (K v)ˣ,
      Units.map (algebraMap F (K v)).toMonoidHom (a i) = (d v).scalar i * q ^ n i :=
    ha i v
  choose q hq using hq
  exact LocalSplitRootsCorrection.isTrivial_of_powerClasses hf n e (d v) a hz' q hq

end Langlands.GroupScheme.IsCentralIsogeny
