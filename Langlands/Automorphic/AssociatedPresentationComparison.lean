import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Automorphic.OperatorLocalRestriction
import Langlands.Automorphic.OperatorCompactCompatibility
import Langlands.Automorphic.PadicLocalCategory
import Langlands.Representation.IsotypicRestriction

noncomputable section

namespace Langlands.CompactSplitting

universe uG uV uW uU

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {U : Type uU} [AddCommGroup U] [Module ℂ U]

/-- The sum of all intertwiner images is preserved by the group action. -/
theorem apply_mem_isotypicPart (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (g : G) {w : W} (hw : w ∈ isotypicPart ρ σ) :
    σ g w ∈ isotypicPart ρ σ := by
  have hle : isotypicPart ρ σ ≤ (isotypicPart ρ σ).comap (σ g) := by
    apply iSup_le
    intro f x hx
    obtain ⟨v, rfl⟩ := hx
    change σ g (f v) ∈ isotypicPart ρ σ
    rw [← Representation.IntertwiningMap.isIntertwining]
    exact range_le_isotypicPart ρ σ f ⟨ρ g v, rfl⟩
  exact hle hw

/-- Postcomposition by an intertwiner preserves a fixed source's isotypic part. -/
theorem intertwiner_mem_isotypicPart (ρ : Representation ℂ G V)
    {σ : Representation ℂ G W} {τ : Representation ℂ G U}
    (L : σ.IntertwiningMap τ) {w : W} (hw : w ∈ isotypicPart ρ σ) :
    L w ∈ isotypicPart ρ τ := by
  have hle : isotypicPart ρ σ ≤ (isotypicPart ρ τ).comap L.toLinearMap := by
    apply iSup_le
    intro f x hx
    obtain ⟨v, rfl⟩ := hx
    exact range_le_isotypicPart ρ τ (L.comp f) ⟨v, rfl⟩
  exact hle hw

/-- An irreducible representation entirely of one irreducible type is equivalent to it. -/
theorem nonempty_equiv_of_isotypicPart_eq_top
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [ρ.IsIrreducible] [σ.IsIrreducible] (h : isotypicPart ρ σ = ⊤) :
    Nonempty (ρ.Equiv σ) := by
  by_contra hne
  have hf (f : ρ.IntertwiningMap σ) : f = 0 := by
    rcases Representation.IsIrreducible.bijective_or_eq_zero f with hb | hz
    · exact (hne ⟨f.ofBijective hb⟩).elim
    · exact hz
  have hbot : isotypicPart ρ σ = ⊥ := by simp [isotypicPart, hf]
  have hzero : (⊤ : Submodule ℂ W) = ⊥ := h.symm.trans hbot
  have : Nontrivial σ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) σ.asModule
  have : Nontrivial W := σ.asModuleEquiv.symm.toEquiv.nontrivial
  exact top_ne_bot hzero

end Langlands.CompactSplitting

namespace Langlands.Global.FiniteAdelicGL

universe u

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

/-- An adelic element trivial at a place commutes with that local factor. -/
theorem commute_localInclusion_of_projection_eq_one (v : FinitePlace F)
    (d : FiniteAdelicGL F n) (hd : localProjection F n v d = 1)
    (g : FiniteLocalGL F n v) :
    Commute d (localInclusion F n v g) := by
  change d * localInclusion F n v g = localInclusion F n v g * d
  apply ext_localProjection F n
  intro w
  simp only [map_mul]
  by_cases hw : w = v
  · subst w
    simp only [hd, one_mul, mul_one]
  · rw [localProjection_localInclusion_of_ne F n v w hw]
    simp only [one_mul, mul_one]

end Langlands.Global.FiniteAdelicGL

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.CompactSplitting

universe u uV uW

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance associatedComparisonRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance associatedComparisonContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance associatedComparisonSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance associatedComparisonFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance associatedComparisonStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance associatedComparisonOperatorGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance associatedComparisonLocalGroup (v : FinitePlace F) (L : LocalRealization F n v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

namespace OperatorRealization

/-- Stability under the three actual operator families implies full stability. -/
theorem invariant_of_generators (S : OperatorRealization F n) (P : Submodule ℂ S.Space)
    (hd : ∀ d x, x ∈ P → S.finiteRepresentation d x ∈ P)
    (hk : ∀ k x, x ∈ P → S.compactRepresentation k x ∈ P)
    (hu : ∀ a x, x ∈ P → S.envelopingAction a x ∈ P) :
    ∀ a x, x ∈ P → S.representation a x ∈ P := by
  intro a
  refine Algebra.adjoin_induction
    (p := fun a ha => ∀ x, x ∈ P → S.operatorAction ⟨a, ha⟩ x ∈ P)
    ?_ ?_ ?_ ?_ a.property
  · rintro a ((⟨d, rfl⟩ | ⟨k, rfl⟩) | ⟨u, rfl⟩)
    · exact hd d
    · exact hk k
    · exact hu u
  · intro c x hx
    change c • x ∈ P
    exact P.smul_mem c hx
  · intro a b ha hb hLa hLb x hx
    change a ∈ automorphicOperatorAlgebra F n at ha
    change b ∈ automorphicOperatorAlgebra F n at hb
    change S.operatorAction (⟨a, ha⟩ + ⟨b, hb⟩) x ∈ P
    have he : S.operatorAction (⟨a, ha⟩ + ⟨b, hb⟩) =
        S.operatorAction ⟨a, ha⟩ + S.operatorAction ⟨b, hb⟩ :=
      S.operatorAction.map_add _ _
    exact (congrArg (fun A : Module.End ℂ S.Space => A x ∈ P) he).mpr
      (P.add_mem (hLa x hx) (hLb x hx))
  · intro a b ha hb hLa hLb x hx
    change a ∈ automorphicOperatorAlgebra F n at ha
    change b ∈ automorphicOperatorAlgebra F n at hb
    change S.operatorAction (⟨a, ha⟩ * ⟨b, hb⟩) x ∈ P
    simpa only [map_mul, Module.End.mul_apply] using hLa _ (hLb x hx)

/-- A local isotypic part is stable under all actual automorphic operators. -/
theorem isotypicPart_invariant (S : OperatorRealization F n) (v : FinitePlace F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (FiniteLocalGL F n v) V) :
    ∀ a x, x ∈ isotypicPart ρ (S.localRepresentation v) →
      S.representation a x ∈ isotypicPart ρ (S.localRepresentation v) := by
  apply S.invariant_of_generators
  · intro d x hx
    let d₀ := d * (localInclusion F n v (localProjection F n v d))⁻¹
    have hd₀ : localProjection F n v d₀ = 1 := by
      simp only [d₀, map_mul, map_inv, localProjection_localInclusion, mul_inv_cancel]
    let A : (S.localRepresentation v).IntertwiningMap (S.localRepresentation v) :=
      { toLinearMap := S.finiteRepresentation d₀
        isIntertwining' := fun g => by
          change S.finiteRepresentation d₀ *
              S.finiteRepresentation (localInclusion F n v g) =
            S.finiteRepresentation (localInclusion F n v g) * S.finiteRepresentation d₀
          exact ((commute_localInclusion_of_projection_eq_one v d₀ hd₀ g).map
            S.finiteRepresentation).eq }
    have hm := intertwiner_mem_isotypicPart ρ A
      (apply_mem_isotypicPart ρ (S.localRepresentation v) (localProjection F n v d) hx)
    change S.finiteRepresentation d₀
      (S.finiteRepresentation (localInclusion F n v (localProjection F n v d)) x) ∈
        isotypicPart ρ (S.localRepresentation v) at hm
    have he : d₀ * localInclusion F n v (localProjection F n v d) = d := by
      simp only [d₀, mul_assoc, inv_mul_cancel, mul_one]
    simpa only [← Module.End.mul_apply, ← map_mul, he] using hm
  · intro k x hx
    let A : (S.localRepresentation v).IntertwiningMap (S.localRepresentation v) :=
      { toLinearMap := S.compactRepresentation k
        isIntertwining' := fun g => LinearMap.ext (fun f =>
          (S.finiteRepresentation_compactRepresentation (localInclusion F n v g) k f).symm) }
    exact intertwiner_mem_isotypicPart ρ A hx
  · intro a x hx
    let A : (S.localRepresentation v).IntertwiningMap (S.localRepresentation v) :=
      { toLinearMap := S.envelopingAction a
        isIntertwining' := fun g => LinearMap.ext (fun f =>
          (S.finiteRepresentation_envelopingAction (localInclusion F n v g) a f).symm) }
    exact intertwiner_mem_isotypicPart ρ A hx

/-- Full irreducibility makes every nonzero local isotypic part exhaustive. -/
theorem isotypicPart_eq_top_of_ne_bot (S : OperatorRealization F n)
    [S.IsIrreducible] (v : FinitePlace F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (FiniteLocalGL F n v) V)
    (h : isotypicPart ρ (S.localRepresentation v) ≠ ⊥) :
    isotypicPart ρ (S.localRepresentation v) = ⊤ := by
  let P : Subrepresentation S.representation :=
    { toSubmodule := isotypicPart ρ (S.localRepresentation v)
      apply_mem_toSubmodule := S.isotypicPart_invariant v ρ }
  rcases eq_bot_or_eq_top P with hp | hp
  · exact (h (congrArg Subrepresentation.toSubmodule hp)).elim
  · exact congrArg Subrepresentation.toSubmodule hp

/-- Irreducible local representations embedding in the same full irreducible
realization are equivalent, even with independent carrier universes. -/
theorem nonempty_local_equiv_of_injective (S : OperatorRealization F n)
    [S.IsIrreducible] (v : FinitePlace F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (FiniteLocalGL F n v) V)
    (σ : Representation ℂ (FiniteLocalGL F n v) W)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    (f : ρ.IntertwiningMap (S.localRepresentation v)) (hf : Function.Injective f)
    (g : σ.IntertwiningMap (S.localRepresentation v)) (hg : Function.Injective g) :
    Nonempty (ρ.Equiv σ) := by
  have : Nontrivial ρ.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (FiniteLocalGL F n v)) ρ.asModule
  have : Nontrivial V := ρ.asModuleEquiv.symm.toEquiv.nontrivial
  have hne : isotypicPart ρ (S.localRepresentation v) ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hm := range_le_isotypicPart ρ (S.localRepresentation v) f
      (show f x ∈ LinearMap.range f.toLinearMap from ⟨x, rfl⟩)
    rw [hbot, Submodule.mem_bot] at hm
    exact hx (hf (hm.trans (map_zero f).symm))
  have htop := S.isotypicPart_eq_top_of_ne_bot v ρ hne
  apply nonempty_equiv_of_isotypicPart_eq_top
  rw [← isotypicPart_comap_of_injective ρ σ (S.localRepresentation v) g hg,
    htop, Submodule.comap_top]

/-- An actual local subspace in the finite image embeds in the whole realization. -/
def localSubspaceInclusion (S : OperatorRealization F n) (v : FinitePlace F)
    (L : LocalRealization F n v) (hL : L ≤ S.toFiniteRealization.toLocal F n v) :
    L.representation.IntertwiningMap (S.localRepresentation v) :=
  (S.localFormEquiv v).symm.toIntertwiningMap.comp
    { toLinearMap :=
        { toFun := fun x => ⟨x.val, hL x.property⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => by ext; rfl }

theorem localSubspaceInclusion_injective (S : OperatorRealization F n) (v : FinitePlace F)
    (L : LocalRealization F n v) (hL : L ≤ S.toFiniteRealization.toLocal F n v) :
    Function.Injective (S.localSubspaceInclusion v L hL) := by
  intro x y h
  change (S.localFormEquiv v).symm _ = (S.localFormEquiv v).symm _ at h
  have hh := (S.localFormEquiv v).symm.injective h
  have hv : x.val = y.val := congrArg
    (fun z : (S.toFiniteRealization.toLocal F n v).Space => z.val) hh
  exact Subtype.ext hv

end OperatorRealization

namespace CuspidalSpectralPresentation

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}
  {S : CuspidalOperatorRealization F r}

/-- Each local component of a spectral presentation lies in the full finite image. -/
theorem localComponent_le_full (P : CuspidalSpectralPresentation.{u, uV} S)
    (v : FinitePlace F) :
    P.localComponent v ≤ S.realization.toFiniteRealization.toLocal F (r + 1) v := by
  intro f hf
  exact P.finiteSlice.le_image
    (P.presentation.localComponent_le P.finiteSlice.nonzero v hf)

/-- Two arbitrary presentations of a full cuspidal realization have equivalent
irreducible local components. The two presentation universes are independent. -/
theorem nonempty_localComponent_equiv
    (P : CuspidalSpectralPresentation.{u, uV} S)
    (Q : CuspidalSpectralPresentation.{u, uW} S) (v : FinitePlace F)
    (hP : (P.localComponent v).IsIrreducible)
    (hQ : (Q.localComponent v).IsIrreducible) :
    Nonempty ((P.localComponent v).representation.Equiv
      (Q.localComponent v).representation) := by
  have : S.realization.IsIrreducible := S.irreducible
  have : (P.localComponent v).representation.IsIrreducible := hP
  have : (Q.localComponent v).representation.IsIrreducible := hQ
  exact S.realization.nonempty_local_equiv_of_injective v
    (P.localComponent v).representation (Q.localComponent v).representation
    (S.realization.localSubspaceInclusion v _ (P.localComponent_le_full v))
    (S.realization.localSubspaceInclusion_injective v _ (P.localComponent_le_full v))
    (S.realization.localSubspaceInclusion v _ (Q.localComponent_le_full v))
    (S.realization.localSubspaceInclusion_injective v _ (Q.localComponent_le_full v))

/-- The local smooth class is independent of the chosen irreducible presentation. -/
theorem localComponent_isoClass_eq
    (P : CuspidalSpectralPresentation.{u, uV} S)
    (Q : CuspidalSpectralPresentation.{u, uW} S) (v : FinitePlace F)
    (hP : (P.localComponent v).IsIrreducible)
    (hQ : (Q.localComponent v).IsIrreducible) :
    (P.localComponent v).isoClass = (Q.localComponent v).isoClass :=
  ((P.localComponent v).isoClass_eq_iff _).mpr (P.nonempty_localComponent_equiv Q v hP hQ)

/-- The equality uses the canonical p-adic topology and the original local actions. -/
theorem localComponent_padicClass_eq
    (P : CuspidalSpectralPresentation.{u, uV} S)
    (Q : CuspidalSpectralPresentation.{u, uW} S) (v : FinitePlace F)
    (hP : (P.localComponent v).IsIrreducible) (hAP : (P.localComponent v).IsAdmissible)
    (hQ : (Q.localComponent v).IsIrreducible) (hAQ : (Q.localComponent v).IsAdmissible) :
    (P.localComponent v).padicClass hP hAP = (Q.localComponent v).padicClass hQ hAQ :=
  ((P.localComponent v).padicClass_eq_iff _ hP hAP hQ hAQ).mpr
    (P.nonempty_localComponent_equiv Q v hP hQ)

end CuspidalSpectralPresentation

end Langlands.Automorphic
