import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # The rank-one locus and its full-fibre base open -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

variable {X Y S : Scheme.{u}}

/-- The union of all open subsets on which the actual module sheaf is trivial. -/
def rankOneLocus (M : X.Modules) : X.Opens :=
  ⨆ (U : X.Opens)
    (_ : Nonempty (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)), U

lemma mem_rankOneLocus (M : X.Modules) (x : X) :
    x ∈ rankOneLocus M ↔ ∃ U : X.Opens, x ∈ U ∧
      Nonempty (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  simp only [rankOneLocus, Opens.mem_iSup]
  constructor
  · rintro ⟨U, hU, hx⟩
    exact ⟨U, hx, hU⟩
  · rintro ⟨U, hx, hU⟩
    exact ⟨U, hU, hx⟩

/-- The locus depends only on the isomorphism class of the module sheaf. -/
lemma rankOneLocus_eq_of_iso {M N : X.Modules} (e : M ≅ N) :
    rankOneLocus M = rankOneLocus N := by
  have forward {M N : X.Modules} (e : M ≅ N) :
      rankOneLocus M ≤ rankOneLocus N := by
    intro x hx
    obtain ⟨U, hxU, ⟨t⟩⟩ := (mem_rankOneLocus M x).mp hx
    exact (mem_rankOneLocus N x).mpr
      ⟨U, hxU, ⟨((Scheme.Modules.restrictFunctor U.ι).mapIso e).symm ≪≫ t⟩⟩
  exact le_antisymm (forward e) (forward e.symm)

lemma rankOneLocus_eq_top_iff (M : X.Modules) :
    rankOneLocus M = ⊤ ↔ IsLocallyFreeRankOne M := by
  constructor
  · intro h x
    apply (mem_rankOneLocus M x).mp
    rw [h]
    trivial
  · intro h
    apply top_unique
    intro x _
    exact (mem_rankOneLocus M x).mpr (h x)

/-- A local trivialization pulls back to a local trivialization. -/
lemma preimage_rankOneLocus_le (f : X ⟶ Y) (M : Y.Modules) :
    f ⁻¹ᵁ rankOneLocus M ≤ rankOneLocus ((Scheme.Modules.pullback f).obj M) := by
  intro x hx
  obtain ⟨U, hxU, ⟨e⟩⟩ := (mem_rankOneLocus M (f x)).mp hx
  apply (mem_rankOneLocus _ x).mpr
  exact ⟨f ⁻¹ᵁ U, hxU, ⟨restrictPullbackIso f U M ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso e ≪≫
      Langlands.Scheme.Modules.pullbackUnitIso (f ∣_ U)⟩⟩

/-- A morphism with image in the rank-one locus pulls the module back to a
locally free rank-one sheaf. -/
lemma isLocallyFreeRankOne_pullback_of_mem (f : X ⟶ Y) (M : Y.Modules)
    (h : ∀ x : X, f x ∈ rankOneLocus M) :
    IsLocallyFreeRankOne ((Scheme.Modules.pullback f).obj M) := by
  intro x
  exact (mem_rankOneLocus _ x).mp (preimage_rankOneLocus_le f M (h x))

/-- Restriction to any open contained in the locus is a line bundle. -/
lemma isLocallyFreeRankOne_restrict_of_le (M : X.Modules) (U : X.Opens)
    (h : U ≤ rankOneLocus M) : IsLocallyFreeRankOne (M.restrict U.ι) := by
  have h' := isLocallyFreeRankOne_pullback_of_mem U.ι M (fun x ↦ h x.property)
  exact h'.of_iso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm

/-- The actual line bundle obtained by restricting to the rank-one locus. -/
def lineBundleOnRankOneLocus (M : X.Modules) : LineBundle (rankOneLocus M).toScheme :=
  ⟨M.restrict (rankOneLocus M).ι,
    isLocallyFreeRankOne_restrict_of_le M _ le_rfl⟩

/-- The complement of the closed image of the failure of local rank one.
Universal closedness, in particular properness, makes this an open subset. -/
def rankOneBaseOpen (f : X ⟶ S) [UniversallyClosed f] (M : X.Modules) : S.Opens :=
  ⟨(f '' (rankOneLocus M : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ (rankOneLocus M).isOpen.isClosed_compl).isOpen_compl⟩

/-- A base point belongs exactly when every point of its full fibre lies in
the rank-one locus. -/
lemma mem_rankOneBaseOpen (f : X ⟶ S) [UniversallyClosed f] (M : X.Modules) (s : S) :
    s ∈ rankOneBaseOpen f M ↔ ∀ x : X, f x = s → x ∈ rankOneLocus M := by
  classical
  constructor
  · intro h x hxs
    by_contra hx
    exact h ⟨x, hx, hxs⟩
  · intro h ⟨x, hx, hxs⟩
    exact hx (h x hxs)

/-- The base open is the largest open whose full inverse image lies in the
rank-one locus. -/
lemma le_rankOneBaseOpen_iff (f : X ⟶ S) [UniversallyClosed f]
    (M : X.Modules) (V : S.Opens) :
    V ≤ rankOneBaseOpen f M ↔ f ⁻¹ᵁ V ≤ rankOneLocus M := by
  constructor
  · intro h x hx
    exact (mem_rankOneBaseOpen f M (f x)).mp (h hx) x rfl
  · intro h s hs
    apply (mem_rankOneBaseOpen f M s).mpr
    intro x hxs
    apply h
    change f x ∈ V
    rw [hxs]
    exact hs

lemma preimage_rankOneBaseOpen_le (f : X ⟶ S) [UniversallyClosed f] (M : X.Modules) :
    f ⁻¹ᵁ rankOneBaseOpen f M ≤ rankOneLocus M :=
  (le_rankOneBaseOpen_iff f M _).mp le_rfl

/-- The original module restricts to a line bundle above the base open. -/
def lineBundleOverRankOneBaseOpen (f : X ⟶ S) [UniversallyClosed f] (M : X.Modules) :
    LineBundle (f ⁻¹ᵁ rankOneBaseOpen f M).toScheme :=
  ⟨M.restrict (f ⁻¹ᵁ rankOneBaseOpen f M).ι,
    isLocallyFreeRankOne_restrict_of_le M _ (preimage_rankOneBaseOpen_le f M)⟩

/-- In a commuting square over a test whose image lies in the base open,
the actual module pullback is locally free of rank one. -/
lemma isLocallyFreeRankOne_pullback_over_baseOpen (f : X ⟶ S) [UniversallyClosed f]
    (M : X.Modules) {X' T : Scheme.{u}} (p : X' ⟶ T) (q : X' ⟶ X) (g : T ⟶ S)
    (comm : p ≫ g = q ≫ f) (h : ∀ t : T, g t ∈ rankOneBaseOpen f M) :
    IsLocallyFreeRankOne ((Scheme.Modules.pullback q).obj M) := by
  apply isLocallyFreeRankOne_pullback_of_mem q M
  intro x
  have hx : f (q x) = g (p x) := congr($(comm.symm) x)
  exact (mem_rankOneBaseOpen f M (g (p x))).mp (h (p x)) (q x) hx

end Langlands.AlgebraicGeometry.Picard
