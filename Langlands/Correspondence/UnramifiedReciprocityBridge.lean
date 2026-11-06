import Langlands.Correspondence.ZeroMonodromyExtension
import Langlands.Correspondence.UnramifiedNormalization

/-!
# Unramified characters under geometric reciprocity and character-sum parameters

For a geometrically normalized reciprocity candidate `e`, the pullback of an
unramified quasi-character `χ` to the actual local Weil group is
`w ↦ χ(ϖ)^(deg w)`. In particular it does not depend on the geometric candidate,
and it is trivial on inertia.

For characters of the Weil group trivial on inertia, the direct sum of the
zero-monodromy character lines exists as a Frobenius-semisimple parameter class in
every carrier universe. It witnesses `IsCharacterSumParameter`, any class with this
property is unique, and it is an unramified parameter class.
-/

noncomputable section

universe uK uG uV uW uι uF uP

namespace Langlands.WeilDeligneRepresentation

section LinearAlgebra

variable {K : Type uK} [Field K] {ι : Type uι} {V : ι → Type uV}
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- Componentwise maps add componentwise. -/
theorem lmap_add (f g : ∀ i, Module.End K (V i)) :
    DirectSum.lmap (fun i => f i + g i) = DirectSum.lmap f + DirectSum.lmap g := by
  apply LinearMap.ext
  intro x
  apply DirectSum.ext
  intro i
  rfl

/-- Polynomials in a componentwise map are computed componentwise. -/
theorem aeval_lmap (f : ∀ i, Module.End K (V i)) (q : Polynomial K) :
    Polynomial.aeval (DirectSum.lmap f) q =
      DirectSum.lmap fun i => Polynomial.aeval (f i) q := by
  induction q using Polynomial.induction_on with
  | C a =>
    apply LinearMap.ext
    intro x
    apply DirectSum.ext
    intro i
    simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
    rfl
  | add p q hp hq =>
    rw [map_add, hp, hq, ← lmap_add]
    simp only [map_add]
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul, h, Polynomial.aeval_X, ← lmap_mul]
    simp only [map_mul, Polynomial.aeval_X]

/-- A componentwise scalar map is semisimple: it is annihilated by the
squarefree polynomial with the distinct scalars as simple roots. -/
theorem isSemisimple_lmap_algebraMap [Fintype ι] (c : ι → K) :
    Module.End.IsSemisimple
      (DirectSum.lmap fun i => algebraMap K (Module.End K (V i)) (c i)) := by
  classical
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := ∏ a ∈ Finset.univ.image c, (Polynomial.X - Polynomial.C a))
  · exact (Polynomial.separable_prod_X_sub_C_iff' (f := fun a => a)).mpr
      (fun _ _ _ _ h => h) |>.squarefree
  · rw [aeval_lmap]
    have h : ∀ i, Polynomial.aeval (algebraMap K (Module.End K (V i)) (c i))
        (∏ a ∈ Finset.univ.image c, (Polynomial.X - Polynomial.C a)) = 0 := by
      intro i
      rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, Polynomial.eval_prod,
        Finset.prod_eq_zero (Finset.mem_image_of_mem c (Finset.mem_univ i)) (by simp),
        map_zero]
    simp only [h]
    exact lmap_zero

end LinearAlgebra

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}

/-- Componentwise pair equivalences give an equivalence of the direct sums. The
two families may have different carrier universes. -/
def directSumCongr {ι : Type uι} [Fintype ι]
    {A : ι → WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : ι → WeilDeligneRepresentation.{uK, uG, uW} K G ν}
    (e : ∀ i, Equiv (A i) (B i)) : Equiv (directSum A) (directSum B) where
  representationEquiv := Representation.Equiv.mk
    (DFinsupp.mapRange.linearEquiv fun i => (e i).representationEquiv.toLinearEquiv)
    (fun g => by
      apply LinearMap.ext
      intro x
      apply DirectSum.ext
      intro i
      exact LinearMap.congr_fun ((e i).representationEquiv.isIntertwining' g)
        ((show DirectSum ι fun i => (A i : Type uV) from x) i))
  comm_monodromy := by
    apply LinearMap.ext
    intro x
    apply DirectSum.ext
    intro i
    exact LinearMap.congr_fun (e i).comm_monodromy
      ((show DirectSum ι fun i => (A i : Type uV) from x) i)

/-- A representation equivalence is an equivalence of the zero-monodromy pairs. The
two carriers may lie in different universes. -/
def zeroMonodromyCongr (ν : G →* Kˣ) {A : FiniteRepresentation.{uK, uG, uV} K G}
    {B : FiniteRepresentation.{uK, uG, uW} K G} (f : FiniteRepresentation.Equiv A B) :
    Equiv (zeroMonodromy ν A) (zeroMonodromy ν B) where
  representationEquiv := f
  comm_monodromy := by
    change f.toLinearMap ∘ₗ 0 = 0 ∘ₗ f.toLinearMap
    rw [LinearMap.comp_zero, LinearMap.zero_comp]

/-- A pair equivalent to a pair with zero monodromy has zero monodromy. -/
theorem monodromy_eq_zero_of_equiv {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν} (f : Equiv A B)
    (hA : A.monodromy = 0) : B.monodromy = 0 := by
  apply LinearMap.ext
  intro b
  have h := LinearMap.congr_fun f.comm_monodromy (f.representationEquiv.symm b)
  rw [hA] at h
  simpa using h.symm

/-- A pair with zero monodromy is equivalent to the zero-monodromy pair on its
underlying representation, by the identity map. -/
def zeroMonodromyEquivOfMonodromyEqZero (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (h : A.monodromy = 0) : Equiv (zeroMonodromy ν A.toFiniteRepresentation) A where
  representationEquiv := Representation.Equiv.refl A.representation
  comm_monodromy := by
    change LinearMap.id ∘ₗ 0 = A.monodromy ∘ₗ LinearMap.id
    rw [h]
    rfl

end Langlands.WeilDeligneRepresentation

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A representation on which inertia acts trivially has open inertia kernel: the
kernel is all of inertia. -/
theorem hasOpenInertiaKernel_of_isUnramified {A : FiniteRepresentation ℂ G}
    {I : Subgroup G} (h : A.IsUnramified I) : A.HasOpenInertiaKernel I := by
  have hk : A.inertiaKernel I = ⊤ := by
    ext x
    simp only [Subgroup.mem_top, iff_true]
    exact h x
  rw [HasOpenInertiaKernel, hk, Subgroup.coe_top]
  exact isOpen_univ

omit [TopologicalSpace G] in
/-- Inertia acts trivially on a representation equivalent to one on which it acts
trivially. -/
theorem isUnramified_of_equiv {A : FiniteRepresentation.{0, uG, uV} ℂ G}
    {B : FiniteRepresentation.{0, uG, uW} ℂ G} (f : Equiv A B) {I : Subgroup G}
    (h : A.IsUnramified I) : B.IsUnramified I := by
  intro i
  apply LinearMap.ext
  intro b
  have hb := LinearMap.congr_fun (f.isIntertwining' (i : G)) (f.symm b)
  rw [h i] at hb
  simpa using hb.symm

omit [TopologicalSpace G] in
/-- The character line of `χ` acts by the scalar `χ g`. -/
theorem characterLine_representation_eq_algebraMap (χ : G →* ℂˣ) (g : G) :
    (characterLine.{uG, uV} χ).representation g =
      algebraMap ℂ (Module.End ℂ (characterLine.{uG, uV} χ)) (χ g : ℂ) := by
  apply LinearMap.ext
  intro v
  rw [Module.algebraMap_end_apply]
  exact characterLine_apply χ g v

end Langlands.FiniteRepresentation

namespace Langlands.Correspondence

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance bridgeFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

section Reciprocity

/-- Under a geometric candidate, the normalized order of the reciprocity image of
`w` is the geometric degree of `w`. -/
theorem ord_reciprocityHom {e : ReciprocityCandidate F} (he : IsGeometricReciprocity F e)
    (w : Weil.Local.localWeilGroup F) :
    F.canonicalTopologicalData.ord (reciprocityHom F e w : F.Carrier) =
      Weil.Local.localDegreeInt F w :=
  congrArg Multiplicative.toAdd
    (DFunLike.congr_fun he.1
      (LocalClassField.WeilQuotients.projection (Weil.Local.localResidueDegree F) w))

/-- Under a geometric candidate, the pullback of an unramified quasi-character is
`w ↦ χ(ϖ)^(deg w)`, for the chosen uniformizer `ϖ`. -/
theorem weilCharacter_apply_of_isUnramified {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) {χ : QuasiCharacter F}
    (hχ : F.canonicalTopologicalData.IsUnramifiedCharacter χ.toMonoidHom)
    (w : Weil.Local.localWeilGroup F) :
    weilCharacter F e χ w =
      χ F.canonicalTopologicalData.uniformizerUnit ^ Weil.Local.localDegreeInt F w := by
  have h := DFunLike.congr_fun
    (F.canonicalTopologicalData.eq_unramifiedCharacter χ.toMonoidHom hχ) (reciprocityHom F e w)
  rw [PadicField.TopologicalData.unramifiedCharacter_apply, ord_reciprocityHom F he] at h
  exact h

/-- Under a geometric candidate, the pullback of an unramified quasi-character is the
unramified Weil character with value `χ(ϖ)` at geometric degree one. -/
theorem weilCharacter_eq_localUnramifiedCharacter {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) {χ : QuasiCharacter F}
    (hχ : F.canonicalTopologicalData.IsUnramifiedCharacter χ.toMonoidHom) :
    weilCharacter F e χ =
      (Weil.Local.localUnramifiedCharacter F
        (χ F.canonicalTopologicalData.uniformizerUnit)).toMonoidHom := by
  ext w
  rw [weilCharacter_apply_of_isUnramified F he hχ]
  rfl

/-- The pullback of an unramified quasi-character is the same for all geometric
candidates. -/
theorem weilCharacter_eq_of_isUnramified {e e' : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) (he' : IsGeometricReciprocity F e')
    {χ : QuasiCharacter F}
    (hχ : F.canonicalTopologicalData.IsUnramifiedCharacter χ.toMonoidHom) :
    weilCharacter F e χ = weilCharacter F e' χ := by
  rw [weilCharacter_eq_localUnramifiedCharacter F he hχ,
    weilCharacter_eq_localUnramifiedCharacter F he' hχ]

/-- Under a geometric candidate, the pullback of an unramified quasi-character is
trivial on inertia. -/
theorem weilCharacter_eq_one_of_mem_localInertia {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) {χ : QuasiCharacter F}
    (hχ : F.canonicalTopologicalData.IsUnramifiedCharacter χ.toMonoidHom)
    {w : Weil.Local.localWeilGroup F} (hw : w ∈ Weil.Local.localInertia F) :
    weilCharacter F e χ w = 1 := by
  change Weil.Local.localDegree F w = 1 at hw
  rw [weilCharacter_apply_of_isUnramified F he hχ, Weil.Local.localDegreeInt, hw]
  rfl

/-- For unramified quasi-characters, being the character-sum parameter does not
depend on the geometric candidate. -/
theorem isCharacterSumParameter_iff_of_isGeometricReciprocity {e e' : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) (he' : IsGeometricReciprocity F e') {r : ℕ}
    {χ : Fin (r + 1) → QuasiCharacter F}
    (hχ : ∀ i, F.canonicalTopologicalData.IsUnramifiedCharacter (χ i).toMonoidHom)
    (D : WeilDeligneClass.{uF, uP} F r.succPNat) :
    IsCharacterSumParameter F e χ D ↔ IsCharacterSumParameter F e' χ D := by
  have h : ∀ i, weilCharacter F e (χ i) = weilCharacter F e' (χ i) := fun i =>
    weilCharacter_eq_of_isUnramified F he he' (hχ i)
  simp only [IsCharacterSumParameter, h]

end Reciprocity

section CharacterSum

/-- The direct sum of the zero-monodromy character lines of a finite family of
characters of the local Weil group, on a carrier in universe `uP`. -/
def characterSumPair {ι : Type} [Fintype ι]
    (ψ : ι → Weil.Local.localWeilGroup F →* ℂˣ) :
    Weil.Local.LocalWeilDeligneRepresentation.{uF, uP} F :=
  WeilDeligneRepresentation.directSum fun i =>
    WeilDeligneRepresentation.zeroMonodromy (Weil.Local.localNormCharacter F).toMonoidHom
      (FiniteRepresentation.characterLine.{uF, uP} (ψ i))

variable {F}

/-- The monodromy of the character-sum pair is zero. -/
theorem characterSumPair_monodromy {ι : Type} [Fintype ι]
    (ψ : ι → Weil.Local.localWeilGroup F →* ℂˣ) :
    (characterSumPair.{uF, uP} F ψ).monodromy = 0 :=
  WeilDeligneRepresentation.lmap_zero

/-- Each Weil element acts on the character sum by the scalar `ψ_i(g)` on the
`i`-th line. -/
theorem characterSumPair_representation {ι : Type} [Fintype ι]
    (ψ : ι → Weil.Local.localWeilGroup F →* ℂˣ) (g : Weil.Local.localWeilGroup F) :
    (characterSumPair.{uF, uP} F ψ).representation g =
      DirectSum.lmap fun i => algebraMap ℂ
        (Module.End ℂ (FiniteRepresentation.characterLine.{uF, uP} (ψ i))) (ψ i g : ℂ) := by
  change (DirectSum.lmap fun i => (FiniteRepresentation.characterLine.{uF, uP} (ψ i)).representation g) = _
  simp only [FiniteRepresentation.characterLine_representation_eq_algebraMap]

/-- Every Weil element acts semisimply on the character sum. -/
theorem characterSumPair_isFrobeniusSemisimple {ι : Type} [Fintype ι]
    (ψ : ι → Weil.Local.localWeilGroup F →* ℂˣ) :
    (characterSumPair.{uF, uP} F ψ).IsFrobeniusSemisimple
      (Weil.Local.localDegree F).toMonoidHom := by
  intro g _
  rw [characterSumPair_representation]
  exact WeilDeligneRepresentation.isSemisimple_lmap_algebraMap _

/-- If every `ψ_i` is trivial on inertia, so is the action on the character sum. -/
theorem characterSumPair_isUnramified {ι : Type} [Fintype ι]
    {ψ : ι → Weil.Local.localWeilGroup F →* ℂˣ}
    (hψ : ∀ i, ∀ w ∈ Weil.Local.localInertia F, ψ i w = 1) :
    (characterSumPair.{uF, uP} F ψ).toFiniteRepresentation.IsUnramified
      (Weil.Local.localInertia F) := by
  intro w
  change (characterSumPair.{uF, uP} F ψ).representation (w : Weil.Local.localWeilGroup F) = 1
  rw [characterSumPair_representation]
  simp only [hψ _ _ w.property, Units.val_one, map_one]
  exact DirectSum.lmap_id

/-- The character sum of characters trivial on inertia is a local Frobenius-semisimple
parameter. -/
theorem characterSumPair_isLocalFrobeniusSemisimpleParameter {ι : Type} [Fintype ι]
    {ψ : ι → Weil.Local.localWeilGroup F →* ℂˣ}
    (hψ : ∀ i, ∀ w ∈ Weil.Local.localInertia F, ψ i w = 1) :
    Weil.Local.IsLocalFrobeniusSemisimpleParameter F (characterSumPair.{uF, uP} F ψ) :=
  ⟨FiniteRepresentation.hasOpenInertiaKernel_of_isUnramified
      (characterSumPair_isUnramified hψ),
    characterSumPair_isFrobeniusSemisimple ψ⟩

/-- The rank of the character sum is the number of characters. -/
theorem characterSumPair_rank {ι : Type} [Fintype ι]
    (ψ : ι → Weil.Local.localWeilGroup F →* ℂˣ) :
    (characterSumPair.{uF, uP} F ψ).rank = Fintype.card ι := by
  rw [characterSumPair, WeilDeligneRepresentation.rank_directSum]
  change ∑ i, (FiniteRepresentation.characterLine.{uF, uP} (ψ i)).rank = _
  simp

/-- The character sum of `r + 1` characters trivial on inertia, as a
Frobenius-semisimple parameter class of rank `r + 1`. -/
def characterSumClass {r : ℕ} (ψ : Fin (r + 1) → Weil.Local.localWeilGroup F →* ℂˣ)
    (hψ : ∀ i, ∀ w ∈ Weil.Local.localInertia F, ψ i w = 1) :
    WeilDeligneClass.{uF, uP} F r.succPNat :=
  ⟨Quotient.mk _ ⟨characterSumPair.{uF, uP} F ψ,
      characterSumPair_isLocalFrobeniusSemisimpleParameter hψ⟩, by
    change (characterSumPair.{uF, uP} F ψ).rank = _
    rw [characterSumPair_rank, Fintype.card_fin, Nat.succPNat_coe, Nat.succ_eq_add_one]⟩

/-- The underlying pair class of `characterSumClass` is the class of the character sum. -/
theorem parameterForget_characterSumClass {r : ℕ}
    (ψ : Fin (r + 1) → Weil.Local.localWeilGroup F →* ℂˣ)
    (hψ : ∀ i, ∀ w ∈ Weil.Local.localInertia F, ψ i w = 1) :
    parameterForget F (characterSumClass.{uF, uP} ψ hψ) =
      WeilDeligneRepresentation.classOf (characterSumPair.{uF, uP} F ψ) :=
  rfl

/-- If the pullbacks of the `χ_i` are trivial on inertia, `characterSumClass` of the
pullbacks is the character-sum parameter of `χ`. -/
theorem isCharacterSumParameter_characterSumClass (e : ReciprocityCandidate F) {r : ℕ}
    (χ : Fin (r + 1) → QuasiCharacter F)
    (hχ : ∀ i, ∀ w ∈ Weil.Local.localInertia F, weilCharacter F e (χ i) w = 1) :
    IsCharacterSumParameter F e χ
      (characterSumClass.{uF, uP} (fun i => weilCharacter F e (χ i)) hχ) :=
  ⟨characterSumPair.{uF, uP} F (fun i => weilCharacter F e (χ i)), rfl,
    ⟨WeilDeligneRepresentation.directSumCongr fun i =>
      WeilDeligneRepresentation.zeroMonodromyCongr _
        (FiniteRepresentation.characterLineEquiv.{uF, uP} (weilCharacter F e (χ i))).symm⟩⟩

/-- For a geometric candidate and unramified quasi-characters, the character-sum
parameter exists in every carrier universe. -/
theorem exists_isCharacterSumParameter {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) {r : ℕ} (χ : Fin (r + 1) → QuasiCharacter F)
    (hχ : ∀ i, F.canonicalTopologicalData.IsUnramifiedCharacter (χ i).toMonoidHom) :
    ∃ D : WeilDeligneClass.{uF, uP} F r.succPNat, IsCharacterSumParameter F e χ D :=
  ⟨_, isCharacterSumParameter_characterSumClass e χ fun i _ hw =>
    weilCharacter_eq_one_of_mem_localInertia F he (hχ i) hw⟩

/-- There is at most one character-sum parameter class of a given family. -/
theorem isCharacterSumParameter_unique (e : ReciprocityCandidate F) {r : ℕ}
    {χ : Fin (r + 1) → QuasiCharacter F} {D D' : WeilDeligneClass.{uF, uP} F r.succPNat}
    (hD : IsCharacterSumParameter F e χ D) (hD' : IsCharacterSumParameter F e χ D') :
    D = D' := by
  obtain ⟨A, hA, ⟨f⟩⟩ := hD
  obtain ⟨A', hA', ⟨f'⟩⟩ := hD'
  apply parameterForget_injective
  rw [← hA, ← hA']
  exact (WeilDeligneRepresentation.classOf_eq_iff A A').mpr ⟨f.symm.trans f'⟩

/-- A character-sum parameter whose characters are trivial on inertia is an
unramified parameter class. -/
theorem isUnramifiedParameterClass_of_isCharacterSumParameter (e : ReciprocityCandidate F)
    {r : ℕ} {χ : Fin (r + 1) → QuasiCharacter F}
    (hχ : ∀ i, ∀ w ∈ Weil.Local.localInertia F, weilCharacter F e (χ i) w = 1)
    {D : WeilDeligneClass.{uF, uP} F r.succPNat} (hD : IsCharacterSumParameter F e χ D) :
    IsUnramifiedParameterClass F D := by
  obtain ⟨A, hA, ⟨f⟩⟩ := hD
  have g := (WeilDeligneRepresentation.directSumCongr fun i =>
    WeilDeligneRepresentation.zeroMonodromyCongr
      (Weil.Local.localNormCharacter F).toMonoidHom
      (FiniteRepresentation.characterLineEquiv.{uF, uP} (weilCharacter F e (χ i)))).trans f
  have h0 : A.monodromy = 0 :=
    WeilDeligneRepresentation.monodromy_eq_zero_of_equiv g (characterSumPair_monodromy _)
  refine ⟨A.toFiniteRepresentation,
    FiniteRepresentation.isUnramified_of_equiv g.representationEquiv
      (characterSumPair_isUnramified hχ), ?_⟩
  rw [← hA]
  exact (WeilDeligneRepresentation.classOf_eq_iff _ _).mpr
    ⟨WeilDeligneRepresentation.zeroMonodromyEquivOfMonodromyEqZero A h0⟩

/-- For a geometric candidate and unramified quasi-characters, every character-sum
parameter is an unramified parameter class. -/
theorem isUnramifiedParameterClass_of_isCharacterSumParameter_of_isGeometricReciprocity
    {e : ReciprocityCandidate F} (he : IsGeometricReciprocity F e) {r : ℕ}
    {χ : Fin (r + 1) → QuasiCharacter F}
    (hχ : ∀ i, F.canonicalTopologicalData.IsUnramifiedCharacter (χ i).toMonoidHom)
    {D : WeilDeligneClass.{uF, uP} F r.succPNat} (hD : IsCharacterSumParameter F e χ D) :
    IsUnramifiedParameterClass F D :=
  isUnramifiedParameterClass_of_isCharacterSumParameter e
    (fun i _ hw => weilCharacter_eq_one_of_mem_localInertia F he (hχ i) hw) hD

end CharacterSum

end Langlands.Correspondence
