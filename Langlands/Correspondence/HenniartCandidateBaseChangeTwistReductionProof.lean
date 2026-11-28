import Langlands.Correspondence.HenniartCandidateBaseChangeFiniteImageReductionStatement
import Langlands.ClassFieldTheory.Local.CommonClosureExistenceProof
import Langlands.Correspondence.HenniartGaloisPullback

/-!
# Proof of the twist reduction of (CI1) for Henniart's candidate

`candidateBaseChangeTwistReduction` proves `CandidateBaseChangeTwistReductionStatement`: for a
cyclic base-change map that commutes with unramified twists, candidate existence reduces (CI1)
for Henniart's candidate to the classes of finite image.
-/

noncomputable section

namespace Langlands.Henniart

universe uK uW uV

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap

namespace Numerical

section DirectSum

variable {G : Type*} [Group G]

/-- Twisting a finite direct sum of representations is equivalent, through the identity of
the carrier, to the direct sum of the twists. -/
def twistDirectSumEquiv (χ : G →* ℂˣ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → FiniteRepresentation.{0, _, uV} ℂ G) :
    FiniteRepresentation.Equiv (FiniteRepresentation.twist χ (FiniteRepresentation.directSum A))
      (FiniteRepresentation.directSum fun i => FiniteRepresentation.twist χ (A i)) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun g => by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    change (χ g : ℂ) • ((FiniteRepresentation.directSum A).representation g
        (DirectSum.lof ℂ ι _ i x)) =
      (FiniteRepresentation.directSum fun i =>
        FiniteRepresentation.twist χ (A i)).representation g (DirectSum.lof ℂ ι _ i x)
    rw [FiniteRepresentation.directSum_representation,
      FiniteRepresentation.directSum_representation]
    erw [DirectSum.lmap_lof, DirectSum.lmap_lof]
    exact (map_smul (DirectSum.lof ℂ ι _ i) (χ g : ℂ) _).symm

/-- Twisting a finite direct sum of classes twists every summand. -/
theorem twistClass_directSumClass (χ : G →* ℂˣ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → FiniteRepresentation.IsomorphismClasses.{0, _, uV} ℂ G) :
    FiniteRepresentation.twistClass χ (FiniteRepresentation.directSumClass c) =
      FiniteRepresentation.directSumClass (fun i => FiniteRepresentation.twistClass χ (c i)) := by
  obtain ⟨A, rfl⟩ : ∃ A : ι → FiniteRepresentation.{0, _, uV} ℂ G,
      c = fun i => FiniteRepresentation.classOf (A i) :=
    ⟨fun i => (c i).out, funext fun i => (Quotient.out_eq (c i)).symm⟩
  rw [FiniteRepresentation.directSumClass_classOf]
  simp only [FiniteRepresentation.twistClass_classOf]
  rw [FiniteRepresentation.directSumClass_classOf]
  exact (FiniteRepresentation.classOf_eq_iff _ _).mpr ⟨twistDirectSumEquiv χ A⟩

/-- Reindexing a direct sum of classes along a cast of `Fin`. -/
theorem directSumClass_fin_cast {n m : ℕ} (h : n = m)
    (c : Fin m → FiniteRepresentation.IsomorphismClasses.{0, _, uV} ℂ G) :
    FiniteRepresentation.directSumClass (fun i : Fin n => c (Fin.cast h i)) =
      FiniteRepresentation.directSumClass c := by
  subst h
  rfl

end DirectSum

variable {p : ℕ} [Fact p.Prime]

/-- The underlying class of an unramified twist is the twist of the underlying class. -/
theorem weilClassForget_weilUnramifiedTwist (K : PadicField.{uK} p) (k : ℕ) (z : ℂˣ)
    (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) :
    weilClassForget K (weilUnramifiedTwist K k z σ) =
      FiniteRepresentation.twistClass
        (Weil.Local.unramifiedCharacter (Weil.Local.localDegree K) z).toMonoidHom
        (weilClassForget K σ) :=
  FiniteRepresentation.forget_continuousIrreducibleTwistClass _ σ.val

/-- The unramified character of `W_L` with value `z`, restricted along the Weil map of the step,
is the unramified character of `W_M` with value `z ^ f(M|L)`. -/
theorem unramifiedCharacter_comp_extensionWeilMap (S : CyclicPrimeStep.{uK} p) (z : ℂˣ) :
    (Weil.Local.unramifiedCharacter (Weil.Local.localDegree S.base) z).toMonoidHom.comp
        (Weil.Local.extensionWeilMap S.base S.top S.embedding).toMonoidHom =
      (Weil.Local.unramifiedCharacter (Weil.Local.localDegree S.top)
        (z ^ S.residueDegree)).toMonoidHom :=
  MonoidHom.ext fun w =>
    Weil.Local.localUnramifiedCharacter_extensionWeilMap S.base S.top S.embedding z w

/-- Twisting `σ` by `z` twists every member of a restriction decomposition by `z ^ f(M|L)`. -/
theorem IsRestrictionDecomposition.weilUnramifiedTwist {S : CyclicPrimeStep.{uK} p} {k : ℕ}
    {σ : IrreducibleWeilClass.{uK, uW} S.base k.succPNat}
    {m : Multiset (Σ j : ℕ, IrreducibleWeilClass.{uK, uW} S.top j.succPNat)}
    (h : IsRestrictionDecomposition S σ m) (z : ℂˣ) :
    IsRestrictionDecomposition S (Numerical.weilUnramifiedTwist S.base k z σ)
      (m.map fun τ => ⟨τ.1, Numerical.weilUnramifiedTwist S.top τ.1 (z ^ S.residueDegree) τ.2⟩) := by
  obtain ⟨l, rfl, hl⟩ := h
  refine ⟨l.map fun τ => ⟨τ.1, Numerical.weilUnramifiedTwist S.top τ.1 (z ^ S.residueDegree) τ.2⟩,
    Multiset.map_coe _ _ |>.symm, ?_⟩
  rw [weilClassForget_weilUnramifiedTwist]
  change FiniteRepresentation.restrictClass _ _ = _
  rw [LocalNumerical.restrictClass_twistClass]
  change FiniteRepresentation.twistClass _ (Weil.Local.extensionRestrictClass S.base S.top S.embedding
    (weilClassForget S.base σ)) = _
  rw [hl, twistClass_directSumClass, unramifiedCharacter_comp_extensionWeilMap,
    ← directSumClass_fin_cast (List.length_map _)]
  congr 1
  funext i
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_map]
  exact (weilClassForget_weilUnramifiedTwist S.top _ _ _).symm

/-- Unramified twists of Weil classes compose by multiplying the values. -/
theorem weilUnramifiedTwist_weilUnramifiedTwist (K : PadicField.{uK} p) (k : ℕ) (a b : ℂˣ)
    (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) :
    weilUnramifiedTwist K k a (weilUnramifiedTwist K k b σ) = weilUnramifiedTwist K k (a * b) σ := by
  have h := Equiv.congr_fun (FiniteRepresentation.continuousIrreducibleTwistEquiv_mul
    (Weil.Local.unramifiedCharacter (Weil.Local.localDegree K) a)
    (Weil.Local.unramifiedCharacter (Weil.Local.localDegree K) b) (k + 1)) σ
  have hc : Weil.Local.unramifiedCharacter (Weil.Local.localDegree K) a *
      Weil.Local.unramifiedCharacter (Weil.Local.localDegree K) b =
      Weil.Local.unramifiedCharacter (Weil.Local.localDegree K) (a * b) :=
    ((Weil.Local.unramifiedCharacterHom (Weil.Local.localDegree K)).map_mul a b).symm
  rw [hc] at h
  exact h

/-- The unramified twist by `1` is the identity. -/
theorem weilUnramifiedTwist_one (K : PadicField.{uK} p) (k : ℕ)
    (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) : weilUnramifiedTwist K k 1 σ = σ := by
  have h1 : Weil.Local.unramifiedCharacter (Weil.Local.localDegree K) 1 = 1 :=
    (Weil.Local.unramifiedCharacterHom (Weil.Local.localDegree K)).map_one
  change FiniteRepresentation.continuousIrreducibleTwistEquiv
    (Weil.Local.unramifiedCharacter (Weil.Local.localDegree K) 1) (k + 1) σ = σ
  rw [h1, FiniteRepresentation.continuousIrreducibleTwistEquiv_one]
  rfl

/-- `Multiset.pmap` over a mapped multiset. -/
theorem multiset_pmap_map {α β γ : Type*} {q : β → Prop} (g : α → β) (f : ∀ b, q b → γ)
    (s : Multiset α) :
    ∀ H : ∀ b ∈ s.map g, q b, Multiset.pmap f (s.map g) H =
      Multiset.pmap (fun a h => f (g a) h) s (fun a ha => H (g a) (Multiset.mem_map_of_mem g ha)) :=
  Quot.inductionOn s fun _ H => congr_arg _ (List.pmap_map H)

end Numerical

open Numerical

/-- Candidate existence reduces (CI1) for a map commuting with unramified twists to the
classes of finite image. -/
theorem candidateBaseChangeTwistReduction :
    CandidateBaseChangeTwistReductionStatement.{uK, uW, uV} := by
  intro hCE p _ S Ch hTw hFin k hL σ m hm hmS
  have hUTI := Extension.unramifiedTwistIndependence_of_reciprocity hCE
    LocalClassField.commonClosureReciprocityExistence
  obtain ⟨z, π₀, b₀, hdec, -⟩ := Extension.rankExtensionBasis_spec S.base hL σ
  set σ₀ := Numerical.weilUnramifiedTwist S.base k z⁻¹ σ with hσ₀
  have hσ : Numerical.weilUnramifiedTwist S.base k z σ₀ = σ := by
    rw [hσ₀, weilUnramifiedTwist_weilUnramifiedTwist, mul_inv_cancel, weilUnramifiedTwist_one]
  have hb₀ : b₀.val = ⟨k.succPNat, σ₀⟩ := Extension.IsStableDecomposition.eq_twist_inv S.base hdec
  have hff : IsFiniteFactoring S.base b₀ := by
    obtain ⟨Q, hQ, hQf, q, hq, -⟩ := hdec.2
    exact ⟨Q, hQ, hQf, q, hq⟩
  have hm₀ := hm.weilUnramifiedTwist z⁻¹
  have hmS₀ : ∀ τ ∈ m.map (fun τ => (⟨τ.1, Numerical.weilUnramifiedTwist S.top τ.1
      (z⁻¹ ^ S.residueDegree) τ.2⟩ : Σ j : ℕ, IrreducibleWeilClass.{uK, uW} S.top j.succPNat)),
      StableExistsAt.{uK, uW, uV, uW} S.top τ.1.succPNat := by
    intro τ hτ
    obtain ⟨τ', hτ', rfl⟩ := Multiset.mem_map.mp hτ
    exact hmS τ' hτ'
  have key := hFin k hL σ₀ ⟨b₀, hb₀, hff⟩ _ hm₀ hmS₀
  calc Ch k (Extension.rankExtension S.base hL σ)
      = Ch k (Extension.rankExtension S.base hL (Numerical.weilUnramifiedTwist S.base k z σ₀)) := by
        rw [hσ]
    _ = Ch k (supercuspidalUnramifiedTwist S.base k z (Extension.rankExtension S.base hL σ₀)) := by
        rw [Extension.rankExtension_twist S.base hL hUTI]
    _ = _ := hTw k z _
    _ = m.pmap (fun τ h => ⟨τ.1, Extension.rankExtension S.top h τ.2⟩) hmS := by
        rw [key, Multiset.map_pmap, multiset_pmap_map]
        refine Multiset.pmap_congr _ fun τ _ h₁ h₂ => ?_
        simp only
        rw [← Extension.rankExtension_twist S.top _ hUTI, weilUnramifiedTwist_weilUnramifiedTwist,
          ← mul_pow, mul_inv_cancel, one_pow, weilUnramifiedTwist_one]

end Langlands.Henniart
