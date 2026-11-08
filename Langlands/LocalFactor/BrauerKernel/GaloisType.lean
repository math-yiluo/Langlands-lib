import Langlands.Correspondence.ArithmeticFactors
import Langlands.LocalFactor.BrauerKernel.TypeChoice
import Langlands.LocalFactor.CommonClosureFiniteQuotient
import Langlands.Representation.Finite.VirtualCharacterProof

/-! # Brauer relations as identities in the representation ring of a finite Galois group -/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianBrauer

open CommonClosure VirtualRepresentation Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

section Restriction

variable (K : Extension F) [Normal F.Carrier K.field]

/-- Restriction of the Galois image of a Weil element to a normal intermediate field. -/
def galoisRestriction : localWeilGroup F →* (K.field ≃ₐ[F.Carrier] K.field) :=
  (AlgEquiv.restrictNormalHom K.field).comp (localProjection F).toMonoidHom

theorem galoisRestriction_apply (w : localWeilGroup F) (x : K.field) :
    ((galoisRestriction F K w x : K.field) : AlgebraicClosure F.Carrier) =
      AlgEquiv.toAlgHom (localProjection F w) (x : AlgebraicClosure F.Carrier) :=
  AlgEquiv.restrictNormal_commutes (localProjection F w) K.field x

theorem galoisRestriction_surjective : Function.Surjective (galoisRestriction F K) := by
  have : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  have : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  apply denseRange_discrete.mp
  exact (AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure F.Carrier)).denseRange.comp
    (localProjection_denseRange F) (InfiniteGalois.restrictNormalHom_continuous K.field)

theorem galoisRestriction_eq_one_iff (w : localWeilGroup F) :
    galoisRestriction F K w = 1 ↔ w ∈ weilSubgroup F K := by
  have hmem : ∀ σ : Gal(AlgebraicClosure F.Carrier/F.Carrier),
      σ ∈ K.field.fixingSubgroup ↔ ∀ x ∈ K.field, σ x = x :=
    fun σ => IntermediateField.mem_fixingSubgroup_iff K.field σ
  change _ ↔ localProjection F w ∈ K.field.fixingSubgroup
  refine Iff.trans ?_ (hmem (localProjection F w)).symm
  constructor
  · intro h x hx
    have hx' := galoisRestriction_apply F K w ⟨x, hx⟩
    rw [h] at hx'
    exact hx'.symm
  · intro h
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [galoisRestriction_apply]
    exact h x x.2

theorem isOpen_ker_galoisRestriction :
    IsOpen ((galoisRestriction F K).ker : Set (localWeilGroup F)) := by
  have hk : (galoisRestriction F K).ker = weilSubgroup F K := by
    ext w
    exact galoisRestriction_eq_one_iff F K w
  rw [hk]
  exact weilSubgroup_open F K

/-- The image in `Gal(K/F)` of the Weil subgroup of an intermediate field. -/
def galoisImage (L : Extension F) : Subgroup (K.field ≃ₐ[F.Carrier] K.field) :=
  (weilSubgroup F L).map (galoisRestriction F K)

theorem galoisRestriction_mem_galoisImage_iff (L : Extension F) (hL : L.field ≤ K.field)
    (w : localWeilGroup F) :
    galoisRestriction F K w ∈ galoisImage F K L ↔ w ∈ weilSubgroup F L := by
  constructor
  · rintro ⟨w', hw', he⟩
    have hk : w'⁻¹ * w ∈ weilSubgroup F K := by
      rw [← galoisRestriction_eq_one_iff, map_mul, map_inv, he, inv_mul_cancel]
    have := (weilSubgroup F L).mul_mem hw' (weilSubgroup_antitone F L K hL hk)
    simpa using this
  · intro hw
    exact ⟨w, hw, rfl⟩

/-- The restriction map from `W_L` onto its Galois image. -/
def toGaloisImage (L : Extension F) : weilSubgroup F L →* galoisImage F K L :=
  ((galoisRestriction F K).comp (weilSubgroup F L).subtype).codRestrict _
    (fun w => ⟨w, w.2, rfl⟩)

theorem toGaloisImage_surjective (L : Extension F) :
    Function.Surjective (toGaloisImage F K L) := by
  rintro ⟨σ, w, hw, rfl⟩
  exact ⟨⟨w, hw⟩, rfl⟩

/-- A character of `W_L` that is trivial on `W_K`, read on the Galois image of `W_L`. -/
def galoisCharacter (L : Extension F) (χ : weilSubgroup F L →* ℂˣ)
    (hχ : ∀ w : weilSubgroup F L, (w : localWeilGroup F) ∈ weilSubgroup F K → χ w = 1) :
    galoisImage F K L →* ℂˣ :=
  (toGaloisImage F K L).liftOfRightInverse (Function.surjInv (toGaloisImage_surjective F K L))
    (Function.rightInverse_surjInv _) ⟨χ, fun w hw => hχ w ((galoisRestriction_eq_one_iff F K w).mp
      (congrArg Subtype.val (MonoidHom.mem_ker.mp hw)))⟩

theorem galoisCharacter_apply (L : Extension F) (χ : weilSubgroup F L →* ℂˣ)
    (hχ : ∀ w : weilSubgroup F L, (w : localWeilGroup F) ∈ weilSubgroup F K → χ w = 1)
    (w : weilSubgroup F L) :
    galoisCharacter F K L χ hχ (toGaloisImage F K L w) = χ w :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ w

end Restriction

/-- The line of a finite-range character has finite image. -/
theorem characterLine_hasFiniteImage {G : Type*} [Group G] (χ : G →* ℂˣ)
    (h : (Set.range χ).Finite) :
    (FiniteRepresentation.characterLine.{_, 0} χ).HasFiniteImage := by
  refine (h.image (fun c : ℂˣ => (c : ℂ) • (LinearMap.id : ULift.{0} ℂ →ₗ[ℂ] ULift.{0} ℂ))).subset ?_
  rintro _ ⟨w, rfl⟩
  refine ⟨χ w, ⟨w, rfl⟩, ?_⟩
  apply LinearMap.ext
  intro v
  rfl

/-- A character whose line acts trivially is trivial. -/
theorem eq_one_of_characterLine_eq_one {G : Type*} [Group G] (χ : G →* ℂˣ) (w : G)
    (h : (FiniteRepresentation.characterLine.{_, 0} χ).representation w = 1) : χ w = 1 := by
  have h1 := congrArg (fun T => (T (ULift.up (1 : ℂ))).down) h
  simp only [FiniteRepresentation.characterLine_apply] at h1
  simp only [ULift.smul_down, smul_eq_mul, mul_one] at h1
  exact Units.ext h1

/-- A finite-range continuous character of `W_L` is trivial on the elements whose Galois
projection lies in some open normal subgroup. -/
theorem exists_galois_kernel_character (L : Extension F) (χ : weilSubgroup F L →ₜ* ℂˣ)
    (hχ : (Set.range χ).Finite) :
    ∃ U : Subgroup (Field.absoluteGaloisGroup F.Carrier), U.Normal ∧
      IsOpen (U : Set (Field.absoluteGaloisGroup F.Carrier)) ∧
      ∀ w : weilSubgroup F L, localProjection F w ∈ U → χ w = 1 := by
  obtain ⟨U, hUn, hUo, hU⟩ := exists_galois_kernel F L
    (FiniteRepresentation.characterLine.{uF, 0} χ.toMonoidHom)
    (FiniteRepresentation.characterLine_isContinuous χ)
    (characterLine_hasFiniteImage χ.toMonoidHom hχ)
  exact ⟨U, hUn, hUo, fun w hw => eq_one_of_characterLine_eq_one χ.toMonoidHom w (hU w hw)⟩

/-- **A finite Galois field trivializing finitely many finite-order characters.** For
finitely many continuous characters `χ_i` of Weil subgroups `W_{L_i}` with finite range,
there is a finite normal intermediate field `K` containing every `L_i` such that every
`χ_i` is trivial on `W_K`. -/
theorem exists_normal_extension_trivializing {ι : Type*} [Finite ι] (L : ι → Extension F)
    (χ : ∀ i, weilSubgroup F (L i) →ₜ* ℂˣ) (hχ : ∀ i, (Set.range (χ i)).Finite) :
    ∃ K : Extension F, Normal F.Carrier K.field ∧ (∀ i, (L i).field ≤ K.field) ∧
      ∀ i (w : weilSubgroup F (L i)), (w : localWeilGroup F) ∈ weilSubgroup F K →
        χ i w = 1 := by
  have : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  have : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  have hB : ∀ i, ∃ U : Subgroup (Field.absoluteGaloisGroup F.Carrier), U.Normal ∧
      IsOpen (U : Set (Field.absoluteGaloisGroup F.Carrier)) ∧
      ∀ w : weilSubgroup F (L i), localProjection F w ∈ U → χ i w = 1 := fun i =>
    exists_galois_kernel_character F (L i) (χ i) (hχ i)
  choose U hUn hUo hU using hB
  let Uc : ι → ClosedSubgroup (Field.absoluteGaloisGroup F.Carrier) := fun i =>
    ⟨U i, (U i).isClosed_of_isOpen (hUo i)⟩
  let N : ι → IntermediateField F.Carrier (AlgebraicClosure F.Carrier) := fun i =>
    IntermediateField.fixedField (U i)
  have hN : ∀ i, (N i).fixingSubgroup = U i := fun i =>
    InfiniteGalois.fixingSubgroup_fixedField (Uc i)
  have : ∀ i, FiniteDimensional F.Carrier (N i) := fun i =>
    (InfiniteGalois.isOpen_iff_finite (N i)).mp (by rw [hN i]; exact hUo i)
  let K₀ : IntermediateField F.Carrier (AlgebraicClosure F.Carrier) :=
    ⨆ i, ((L i).field ⊔ N i)
  let K₁ : IntermediateField F.Carrier (AlgebraicClosure F.Carrier) :=
    IntermediateField.normalClosure F.Carrier K₀ (AlgebraicClosure F.Carrier)
  have hK₀ : K₀ ≤ K₁ := IntermediateField.le_normalClosure K₀
  refine ⟨⟨K₁, inferInstance⟩, inferInstance, fun i => ?_, fun i w hw => ?_⟩
  · exact (le_sup_left.trans (le_iSup (fun i => (L i).field ⊔ N i) i)).trans hK₀
  · apply hU i w
    have hNK : N i ≤ K₁ := (le_sup_right.trans (le_iSup (fun i => (L i).field ⊔ N i) i)).trans hK₀
    rw [← hN i]
    exact IntermediateField.fixingSubgroup_le hNK hw

/-- Inflating, from a finite quotient of `W_E`, the induction of a character `χ` of a
subgroup `S` whose preimage is `W_L` gives the common-closure induction of the line of any
continuous character `η` of `W_L` that agrees with `χ` through the quotient map. -/
theorem inflate_induce_characterLine (E L : Extension F) (h : E.field ≤ L.field)
    {Q : Type uF} [Group Q] [Finite Q] (π : weilSubgroup F E →* Q)
    (hπ : IsOpen (π.ker : Set (weilSubgroup F E))) (hsurj : Function.Surjective π)
    (S : Subgroup Q)
    (hS : ∀ w : weilSubgroup F E, π w ∈ S ↔ (w : localWeilGroup F) ∈ weilSubgroup F L)
    (χ : S →* ℂˣ) (η : weilSubgroup F L →ₜ* ℂˣ)
    (hη : ∀ w : weilSubgroup F L,
      η w = χ ⟨π (Subgroup.inclusion (weilSubgroup_antitone F E L h) w), (hS _).mpr w.2⟩) :
    ExactGrothendieckGroup.inflate.{uF, uF, max uF uV} π hπ
        (FiniteRep.ofClass (FiniteRep.induce S
          (FiniteRep.classOf (FiniteRep.oneDimensional χ)))) =
      induce.{uF, uV} F E L h (ExactGrothendieckGroup.characterClass η) := by
  let T := (weilSubgroup F L).subgroupOf (weilSubgroup F E)
  have hT : ∀ g, g ∈ T ↔ π g ∈ S := fun g => (hS g).symm
  let ν := ContinuousMonoidHom.toContinuousMonoidHom (nestedWeilEquiv F E L h)
  have hP : ∀ A : FiniteRepresentation.{0, uF, max uF uV} ℂ T, A.IsContinuous →
      (FiniteRepresentation.induce T A).IsContinuous :=
    fun _ hA => FiniteRepresentation.isContinuous_induce _ (nestedWeil_open F E L) hA
  rw [ExactGrothendieckGroup.inflate_ofClass_induce π hπ hsurj S T hT hP
    (FiniteRep.oneDimensional χ)
    (FiniteRepresentation.restrict ν.toMonoidHom
      (FiniteRepresentation.characterLine.{uF, max uF uV} η.toMonoidHom))
    (FiniteRepresentation.isContinuous_restrict _ ν.continuous
      (FiniteRepresentation.characterLine_isContinuous η))
    (ULift.moduleEquiv : ULift.{max uF uV} ℂ ≃ₗ[ℂ] ℂ).symm (fun t v => by
      have ht : (χ ⟨π t, (hT t).mp t.2⟩ : ℂ) = (η (ν t) : ℂ) := by
        rw [hη (ν t)]
        rfl
      calc _ = (χ ⟨π t, (hT t).mp t.2⟩ : ℂ) •
            (ULift.moduleEquiv : ULift.{max uF uV} ℂ ≃ₗ[ℂ] ℂ).symm v := rfl
        _ = (η (ν t) : ℂ) • (ULift.moduleEquiv : ULift.{max uF uV} ℂ ≃ₗ[ℂ] ℂ).symm v := by
          rw [ht]
        _ = _ := rfl)]
  change _ = ExactGrothendieckGroup.induce T _ _ _
    (ExactGrothendieckGroup.restrict ν.toMonoidHom _ _ _
      (ExactGrothendieckGroup.ofRepresentation _ ⟨_, _⟩))
  rw [ExactGrothendieckGroup.restrict_ofRepresentation]

end Langlands.LocalFactor.NonabelianBrauer

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

universe uG uQ uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Q : Type uQ} [Group Q]

/-- The trace of the universe lift of a finite coordinate representation is its
character. -/
theorem traceFunction_liftFiniteRepresentation (V : FDRep ℂ Q) :
    FiniteRepresentation.traceFunction (Weil.liftFiniteRepresentation.{uQ, uW} V) =
      V.character := by
  funext q
  change LinearMap.trace ℂ _ ((ULift.moduleEquiv : ULift.{uW} V ≃ₗ[ℂ] V).symm.conj (V.ρ q)) =
    LinearMap.trace ℂ V (V.ρ q)
  exact LinearMap.trace_conj' (V.ρ q) _

/-- **The trace of an inflated virtual representation** is its virtual character
composed with the quotient map. -/
theorem trace_inflate (π : G →* Q) (hπ : IsOpen (π.ker : Set G))
    (x : FiniteRep.VirtualRep ℂ Q) :
    trace (fun A : FiniteRepresentation.{0, uG, uW} ℂ G => A.IsContinuous)
        (inflate.{uG, uQ, uW} π hπ x) =
      fun g => FiniteRep.virtualCharacter (k := ℂ) (G := Q) x (π g) := by
  have h : ((trace (fun A : FiniteRepresentation.{0, uG, uW} ℂ G => A.IsContinuous)).comp
      (inflate.{uG, uQ, uW} π hπ)).toAddMonoidHom =
      ((LinearMap.funLeft ℤ ℂ π).comp
        (FiniteRep.virtualCharacter (k := ℂ) (G := Q))).toAddMonoidHom := by
    apply FiniteRep.completionHom_ext
    intro a
    induction a using Quotient.inductionOn with
    | h V =>
      change trace _ (inflate π hπ (FiniteRep.ofClass (FiniteRep.classOf V))) =
        fun g => FiniteRep.virtualCharacter (k := ℂ) (G := Q)
          (FiniteRep.ofClass (FiniteRep.classOf V)) (π g)
      rw [inflate_ofClass, inflateClass_classOf, trace_ofRepresentation,
        FiniteRep.virtualCharacter_ofClass, FiniteRep.character_classOf]
      change FiniteRepresentation.traceFunction
          (FiniteRepresentation.restrict π (Weil.liftFiniteRepresentation.{uQ, uW} V)) = _
      rw [FiniteRepresentation.traceFunction_restrict, traceFunction_liftFiniteRepresentation]
      rfl
  exact congrArg (fun f => f x) h

end Langlands.VirtualRepresentation.ExactGrothendieckGroup

namespace Langlands.LocalFactor.NonabelianBrauer

open CommonClosure VirtualRepresentation Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The twisted Weil character of `TypeSplit`, as a continuous character. -/
def twistedContinuousCharacter (e : ReciprocityFamily F) (L : Extension F)
    (χ : FieldCharacter F L) (t : ℂ) : weilSubgroup F L →ₜ* ℂˣ :=
  weilCharacter F e L χ * CommonClosureSpectral.character F L (-t)

theorem twistedContinuousCharacter_apply (e : ReciprocityFamily F) (L : Extension F)
    (χ : FieldCharacter F L) (t : ℂ) (w : weilSubgroup F L) :
    twistedContinuousCharacter F e L χ t w = twistedWeilCharacter F e L χ t w := rfl

/-- The trace of an induced character line is its Frobenius sum. -/
theorem trace_induce_characterClass {E : Extension F} (g : Generator F E)
    (η : weilSubgroup F g.extension →ₜ* ℂˣ) (w : weilSubgroup F E) :
    ExactGrothendieckGroup.trace (ContinuousPredicate F E)
        (induce.{uF, uV} F E g.extension g.inclusion (ExactGrothendieckGroup.characterClass η)) w =
      frobeniusSum F g η.toMonoidHom w := by
  rw [CommonClosure.trace_induce, ExactGrothendieckGroup.trace_characterClass]
  rfl

/-- **Galois type decomposition** of an actual relation `z` over the bottom field: a finite
normal intermediate field `K` containing every generator field, exponents `t₁`, `t₂` for the
two characters of every generator, characters `θ₁ g`, `θ₂ g` of the Galois images of the
`W_{L_g}` through which the twisted Weil characters factor, and for every type `τ` the
identity `Σ_g z(g) ([t₁ g = τ] Ind θ₁ g - [t₂ g = τ] Ind θ₂ g) = 0` in the representation
ring of `Gal(K/F)`. -/
structure GaloisTypeDecomposition (e : ReciprocityFamily F)
    (z : Presentation F (Correspondence.baseExtension F)) where
  /-- The finite normal field. -/
  K : Extension F
  normal : Normal F.Carrier K.field
  /-- The exponents of the first characters. -/
  t₁ : Generator F (Correspondence.baseExtension F) → ℂ
  /-- The exponents of the second characters. -/
  t₂ : Generator F (Correspondence.baseExtension F) → ℂ
  le : ∀ g ∈ z.support, g.extension.field ≤ K.field
  /-- The Galois characters of the first characters. -/
  θ₁ : ∀ g : Generator F (Correspondence.baseExtension F),
    @galoisImage p _ F K normal g.extension →* ℂˣ
  /-- The Galois characters of the second characters. -/
  θ₂ : ∀ g : Generator F (Correspondence.baseExtension F),
    @galoisImage p _ F K normal g.extension →* ℂˣ
  θ₁_spec : ∀ g ∈ z.support, ∀ w : weilSubgroup F g.extension,
    θ₁ g (@toGaloisImage p _ F K normal g.extension w) =
      twistedWeilCharacter F e g.extension g.first (t₁ g) w
  θ₂_spec : ∀ g ∈ z.support, ∀ w : weilSubgroup F g.extension,
    θ₂ g (@toGaloisImage p _ F K normal g.extension w) =
      twistedWeilCharacter F e g.extension g.second (t₂ g) w
  identity : ∀ τ : ℂ,
    ∑ g ∈ z.support, z g •
      ((if t₁ g = τ then FiniteRep.ofClass (FiniteRep.induce
          (@galoisImage p _ F K normal g.extension)
          (FiniteRep.classOf (FiniteRep.oneDimensional (θ₁ g)))) else 0) -
        (if t₂ g = τ then FiniteRep.ofClass (FiniteRep.induce
          (@galoisImage p _ F K normal g.extension)
          (FiniteRep.classOf (FiniteRep.oneDimensional (θ₂ g)))) else 0)) =
      (0 : FiniteRep.VirtualRep ℂ (K.field ≃ₐ[F.Carrier] K.field))

theorem mem_weilSubgroup_baseExtension (w : localWeilGroup F) :
    w ∈ weilSubgroup F (Correspondence.baseExtension F) := by
  change Weil.projection (localResidueDegree F) w ∈
    (⊥ : IntermediateField F.Carrier (AlgebraicClosure F.Carrier)).fixingSubgroup
  rw [IntermediateField.fixingSubgroup_bot]
  exact Subgroup.mem_top _

/-- The quotient map from the bottom-field Weil subgroup to `Gal(K/F)`. -/
def bottomGaloisRestriction (K : Extension F) [Normal F.Carrier K.field] :
    weilSubgroup F (Correspondence.baseExtension F) →* (K.field ≃ₐ[F.Carrier] K.field) :=
  (galoisRestriction F K).comp (weilSubgroup F (Correspondence.baseExtension F)).subtype

theorem bottomGaloisRestriction_surjective (K : Extension F) [Normal F.Carrier K.field] :
    Function.Surjective (bottomGaloisRestriction F K) := by
  intro σ
  obtain ⟨w, hw⟩ := galoisRestriction_surjective F K σ
  exact ⟨⟨w, mem_weilSubgroup_baseExtension F w⟩, hw⟩

theorem isOpen_ker_bottomGaloisRestriction (K : Extension F) [Normal F.Carrier K.field] :
    IsOpen ((bottomGaloisRestriction F K).ker :
      Set (weilSubgroup F (Correspondence.baseExtension F))) := by
  rw [bottomGaloisRestriction, ← MonoidHom.comap_ker, Subgroup.coe_comap]
  exact (isOpen_ker_galoisRestriction F K).preimage continuous_subtype_val

/-- **The Galois type identity.** If every type component of a bottom-field relation
vanishes, and the twisted Weil characters factor through `Gal(K/F)`, then each type part is
zero in the representation ring of `Gal(K/F)`. -/
theorem galoisType_identity (e : ReciprocityFamily F)
    (z : Presentation F (Correspondence.baseExtension F)) (t₁ t₂ : Generator F _ → ℂ)
    (htype : ∀ τ w, typeComponent F e z t₁ t₂ τ w = 0)
    (K : Extension F) [Normal F.Carrier K.field] (hle : ∀ g ∈ z.support, g.extension.field ≤ K.field)
    (θ₁ θ₂ : ∀ g : Generator F (Correspondence.baseExtension F),
      galoisImage F K g.extension →* ℂˣ)
    (h₁ : ∀ g ∈ z.support, ∀ w : weilSubgroup F g.extension,
      θ₁ g (toGaloisImage F K g.extension w) =
        twistedWeilCharacter F e g.extension g.first (t₁ g) w)
    (h₂ : ∀ g ∈ z.support, ∀ w : weilSubgroup F g.extension,
      θ₂ g (toGaloisImage F K g.extension w) =
        twistedWeilCharacter F e g.extension g.second (t₂ g) w) (τ : ℂ) :
    ∑ g ∈ z.support, z g •
      ((if t₁ g = τ then FiniteRep.ofClass (FiniteRep.induce (galoisImage F K g.extension)
          (FiniteRep.classOf (FiniteRep.oneDimensional (θ₁ g)))) else 0) -
        (if t₂ g = τ then FiniteRep.ofClass (FiniteRep.induce (galoisImage F K g.extension)
          (FiniteRep.classOf (FiniteRep.oneDimensional (θ₂ g)))) else 0)) =
      (0 : FiniteRep.VirtualRep ℂ (K.field ≃ₐ[F.Carrier] K.field)) := by
  let E := Correspondence.baseExtension F
  let π₀ := bottomGaloisRestriction F K
  have hπ₀ := isOpen_ker_bottomGaloisRestriction F K
  have hS : ∀ g ∈ z.support, ∀ w : weilSubgroup F E,
      π₀ w ∈ galoisImage F K g.extension ↔ (w : localWeilGroup F) ∈ weilSubgroup F g.extension :=
    fun g hg w => galoisRestriction_mem_galoisImage_iff F K _ (hle g hg) w
  have hinf : ∀ g ∈ z.support, ∀ (θ : galoisImage F K g.extension →* ℂˣ) (χ : FieldCharacter F
      g.extension) (t : ℂ), (∀ w : weilSubgroup F g.extension,
        θ (toGaloisImage F K g.extension w) = twistedWeilCharacter F e g.extension χ t w) →
      ExactGrothendieckGroup.trace (ContinuousPredicate F E)
          (ExactGrothendieckGroup.inflate.{uF, uF, uF} π₀ hπ₀
            (FiniteRep.ofClass (FiniteRep.induce (galoisImage F K g.extension)
              (FiniteRep.classOf (FiniteRep.oneDimensional θ))))) =
        fun w => frobeniusSum F g (twistedWeilCharacter F e g.extension χ t) w := by
    intro g hg θ χ t hθ
    rw [inflate_induce_characterLine.{uF, 0} F E g.extension g.inclusion π₀ hπ₀
      (bottomGaloisRestriction_surjective F K) _ (hS g hg) θ
      (twistedContinuousCharacter F e g.extension χ t) (fun w => by
        rw [twistedContinuousCharacter_apply, ← hθ w]
        rfl)]
    funext w
    exact trace_induce_characterClass.{uF, 0} F g _ w
  have hterm : ∀ g ∈ z.support, ∀ w : weilSubgroup F E,
      ExactGrothendieckGroup.trace (ContinuousPredicate F E)
        (ExactGrothendieckGroup.inflate.{uF, uF, uF} π₀ hπ₀ (z g •
          ((if t₁ g = τ then FiniteRep.ofClass (FiniteRep.induce (galoisImage F K g.extension)
              (FiniteRep.classOf (FiniteRep.oneDimensional (θ₁ g)))) else 0) -
            (if t₂ g = τ then FiniteRep.ofClass (FiniteRep.induce (galoisImage F K g.extension)
              (FiniteRep.classOf (FiniteRep.oneDimensional (θ₂ g)))) else 0)))) w =
        (z g : ℂ) * ((if t₁ g = τ then
            frobeniusSum F g (twistedWeilCharacter F e g.extension g.first (t₁ g)) w else 0) -
          (if t₂ g = τ then
            frobeniusSum F g (twistedWeilCharacter F e g.extension g.second (t₂ g)) w else 0)) := by
    intro g hg w
    rw [map_zsmul, map_zsmul, map_sub, map_sub, Pi.smul_apply, Pi.sub_apply, zsmul_eq_mul]
    congr 2
    · split_ifs
      · exact congrFun (hinf g hg (θ₁ g) g.first (t₁ g) (h₁ g hg)) w
      · rw [map_zero, map_zero]
        rfl
    · split_ifs
      · exact congrFun (hinf g hg (θ₂ g) g.second (t₂ g) (h₂ g hg)) w
      · rw [map_zero, map_zero]
        rfl
  apply FiniteRep.VirtualCharacter.faithfulness (G := K.field ≃ₐ[F.Carrier] K.field)
  rw [map_zero]
  funext σ
  obtain ⟨w, rfl⟩ := bottomGaloisRestriction_surjective F K σ
  rw [← congrFun (ExactGrothendieckGroup.trace_inflate.{uF, uF, uF} π₀ hπ₀ _) w]
  change _ = (0 : ℂ)
  rw [map_sum, map_sum, Finset.sum_apply]
  refine (Finset.sum_congr rfl fun g hg => hterm g hg w).trans ?_
  exact htype τ w

/-- **Every actual relation over the bottom field has a Galois type decomposition.** -/
theorem nonempty_galoisTypeDecomposition (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (z : Presentation F (Correspondence.baseExtension F))
    (hz : presentationMap.{uF, uV} F e _ z = 0) :
    Nonempty (GaloisTypeDecomposition F e z) := by
  classical
  obtain ⟨t₁, t₂, h₁, h₂, -, htype⟩ := exists_typeComponent_eq_zero.{uF, uV} F e he _ z hz
  let ι := z.support × Bool
  let L : ι → Extension F := fun i => i.1.1.extension
  let χ : ∀ i : ι, weilSubgroup F (L i) →ₜ* ℂˣ := fun i =>
    if i.2 then twistedContinuousCharacter F e i.1.1.extension i.1.1.first (t₁ i.1.1)
    else twistedContinuousCharacter F e i.1.1.extension i.1.1.second (t₂ i.1.1)
  have hχ : ∀ i, (Set.range (χ i)).Finite := by
    rintro ⟨⟨g, hg⟩, b⟩
    cases b
    · exact h₂ g hg
    · exact h₁ g hg
  obtain ⟨K, hK, hle, htriv⟩ := exists_normal_extension_trivializing F L χ hχ
  let := hK
  let θ₁ : ∀ g : Generator F (Correspondence.baseExtension F),
      galoisImage F K g.extension →* ℂˣ := fun g =>
    if hg : g ∈ z.support then
      galoisCharacter F K g.extension (twistedWeilCharacter F e g.extension g.first (t₁ g))
        (fun w hw => htriv ⟨⟨g, hg⟩, true⟩ w hw)
    else 1
  let θ₂ : ∀ g : Generator F (Correspondence.baseExtension F),
      galoisImage F K g.extension →* ℂˣ := fun g =>
    if hg : g ∈ z.support then
      galoisCharacter F K g.extension (twistedWeilCharacter F e g.extension g.second (t₂ g))
        (fun w hw => htriv ⟨⟨g, hg⟩, false⟩ w hw)
    else 1
  have hθ₁ : ∀ g ∈ z.support, ∀ w : weilSubgroup F g.extension,
      θ₁ g (toGaloisImage F K g.extension w) =
        twistedWeilCharacter F e g.extension g.first (t₁ g) w := by
    intro g hg w
    simp only [θ₁, hg, ↓reduceDIte]
    exact galoisCharacter_apply F K _ _ _ w
  have hθ₂ : ∀ g ∈ z.support, ∀ w : weilSubgroup F g.extension,
      θ₂ g (toGaloisImage F K g.extension w) =
        twistedWeilCharacter F e g.extension g.second (t₂ g) w := by
    intro g hg w
    simp only [θ₂, hg, ↓reduceDIte]
    exact galoisCharacter_apply F K _ _ _ w
  have hle' : ∀ g ∈ z.support, g.extension.field ≤ K.field := fun g hg => hle ⟨⟨g, hg⟩, true⟩
  exact ⟨⟨K, hK, t₁, t₂, hle', θ₁, θ₂, hθ₁, hθ₂,
    galoisType_identity F e z t₁ t₂ htype K hle' θ₁ θ₂ hθ₁ hθ₂⟩⟩

end Langlands.LocalFactor.NonabelianBrauer
