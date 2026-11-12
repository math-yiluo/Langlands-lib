import Langlands.Correspondence.HenniartExtensionTwist
import Langlands.Correspondence.AssemblyDeterminant

/-!
# Determinants, central characters and the extended stable map

The determinant clause of a candidate gives `ω_π₀ ∘ rec = det b₀` for a stable
image `π₀` of `b₀`. Twisting by the unramified character with value `z`
multiplies the determinant of a class of dimension `n` by the `n`-th power of
that character, and multiplies the central character of a supercuspidal class
of `GL_n` by the `n`-th power of the corresponding field character. Under a
geometric candidate these agree, so the extended map is compatible with
determinants and central characters.
-/

noncomputable section

namespace Langlands.FiniteRepresentation

universe uG uV

variable {G : Type uG} [Group G]

/-- The determinant of a twist of a class of rank `n` is multiplied by `χ ^ n`. -/
theorem determinantCharacterClass_twistClass (χ : G →* ℂˣ)
    (c : IsomorphismClasses.{0, uG, uV} ℂ G) :
    determinantCharacterClass (twistClass χ c) = χ ^ classRank c * determinantCharacterClass c := by
  induction c using Quotient.inductionOn with
  | h A =>
    ext g
    change LinearMap.det ((χ g : ℂ) • A.representation g) =
      ((χ g ^ A.rank * determinantCharacter A g : ℂˣ) : ℂ)
    rw [LinearMap.det_smul]
    push_cast
    rfl

end Langlands.FiniteRepresentation

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap

universe uK uW uV uE

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance henniartExtensionDeterminantFieldTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

local instance henniartExtensionDeterminantGLTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n K.Carrier) :=
  K.canonicalGeneralLinearTopology n

/-- Central action on a supercuspidal class is central action on a representative. -/
theorem supercuspidalCentralActsBy_iff {n : ℕ+}
    (A : GeneralLinear.SupercuspidalRep.{uK, uV} (F := K.Carrier) (n := (n : ℕ)))
    (a : K.Carrierˣ) (c : ℂˣ) :
    SupercuspidalCentralActsBy K (n := n) A.isoClass a c ↔
      ∀ v : A.obj, A.obj.representation (GeneralLinear.scalar a) v = (c : ℂ) • v := by
  constructor
  · intro h v
    exact AssemblyDeterminant.centralActsBy_apply K h A.toIrreducibleAdmissible rfl v
  · intro h
    exact ⟨A.toIrreducibleAdmissible, rfl, h⟩

/-- Twisting by `χ ∘ det` multiplies the central action of `a` by `χ(a) ^ n`. -/
theorem supercuspidalCentralActsBy_twist {n : ℕ+} {π : SupercuspidalAutomorphicClass.{uK, uV} K n}
    {a : K.Carrierˣ} {c : ℂˣ} (h : SupercuspidalCentralActsBy K π a c) (χ : QuasiCharacter K) :
    SupercuspidalCentralActsBy K (supercuspidalTwist K χ π) a (χ a ^ (n : ℕ) * c) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep π
  have hA := (supercuspidalCentralActsBy_iff K A a c).mp h
  change SupercuspidalCentralActsBy K (n := n)
    (GeneralLinear.SupercuspidalRep.twist _ _ _ A).isoClass a _
  rw [supercuspidalCentralActsBy_iff]
  have key : ∀ u : A.obj, ((determinantQuasiCharacter K n χ (GeneralLinear.scalar a) : ℂˣ) : ℂ) •
      A.obj.representation (GeneralLinear.scalar a) u = ((χ a ^ (n : ℕ) * c : ℂˣ) : ℂ) • u := by
    intro u
    rw [hA u, smul_smul]
    congr 1
    change ((χ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) a)) :
      ℂˣ) : ℂ) * c = ((χ a ^ (n : ℕ) * c : ℂˣ) : ℂ)
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow]
    push_cast
    rfl
  intro v
  exact key v

/-- Determinant compatibility of the extended stable map. -/
theorem extensionMap_determinant (hSC : StableCorrespondenceStatement.{uK, uW, uV, uE})
    {e : ReciprocityCandidate K} (he : IsGeometricReciprocity K e) :
    SupercuspidalDeterminantCompatibility K e (extensionMap K hSC) := by
  intro n σ w
  obtain ⟨z, π₀, b₀, h, he₁⟩ := extensionBasis_spec K hSC ⟨n, σ⟩
  obtain ⟨Q, _, _, q, hσ, ⟨W, A, Φ, hΦ⟩, hall⟩ := h.2
  have hΦx := hall W A Φ hΦ ⟨generator b₀, hΦ.1 hσ⟩ rfl
  obtain ⟨ω, hω, hωdet⟩ := hΦ.2.2.1 e he ⟨generator b₀, hΦ.1 hσ⟩
  rw [hΦx, PadicSupercuspidal.isUnitaryCentralCharacter_generator_iff] at hω
  rw [LocalWeil.unitaryDeterminant_generator] at hωdet
  -- the rank of `b₀`
  have hrank : b₀.val.1 = n := by
    have := congrArg Sigma.fst h.1
    simpa using this
  -- reduce to the components of `π₀`
  obtain ⟨⟨m, π'⟩, hπ'⟩ := π₀
  have hm : m = n := by
    have := extensionBasis_rank K hSC ⟨n, σ⟩
    rw [he₁] at this
    exact this
  subst hm
  have hc : extensionMap K hSC m σ = supercuspidalTwist K (fieldUnramified K z) π' := by
    have h1 := (sigma_extensionMap K hSC m σ).trans he₁
    exact eq_of_heq (Sigma.mk.inj h1).2
  rw [hc]
  have hcentral := supercuspidalCentralActsBy_twist K (hω (reciprocityHom K e w))
    (fieldUnramified K z)
  convert hcentral using 1
  -- the Weil determinant of the twist
  have hforget : weilClassForget K σ = FiniteRepresentation.twistClass
      (Weil.Local.localUnramifiedCharacter K z).toMonoidHom
      (Weil.underlyingClass _ b₀.val) := by
    rw [← Weil.underlyingClass_twistBasisEquiv, h.1]
    rfl
  have hclassRank : FiniteRepresentation.classRank (Weil.underlyingClass _ b₀.val) = (m : ℕ) := by
    rw [Weil.classRank_underlyingClass, hrank]
  rw [irreducibleWeilDeterminant, hforget,
    FiniteRepresentation.determinantCharacterClass_twistClass,
    hclassRank, MonoidHom.mul_apply, MonoidHom.pow_apply]
  have hdet := hωdet w
  change ω (reciprocityHom K e w) =
    FiniteRepresentation.determinantCharacterClass (Weil.underlyingClass _ b₀.val) w at hdet
  rw [← hdet]
  congr 1
  rw [fieldUnramified_apply, ord_reciprocityHom K he]
  rfl

end Langlands.Henniart.Extension
