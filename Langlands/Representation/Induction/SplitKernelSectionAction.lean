import Langlands.Representation.Jacquet.LocalizationTransport

/-! Elementary section actions on actual character-localized kernel quotients. -/

noncomputable section

namespace Langlands.Induction.SplitKernelLocalization

universe uR uG uL uV uW uX

variable {R : Type uR} [CommRing R]
variable {G : Type uG} {L : Type uL} [Group G] [Group L]
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [AddCommGroup X] [Module R X]

/-- The inverse section conjugation has values in the actual kernel. -/
def inverseSectionConjugate (r : G →* L) (s : L →* G) (l : L) (n : r.ker) : r.ker :=
  ⟨(s l)⁻¹ * n * s l, by
    change r ((s l)⁻¹ * n * s l) = 1
    have hn : r n = 1 := n.property
    simp [hn]⟩

/-- Stability is proved on generators using inverse section conjugation at `l⁻¹`. -/
theorem sectionRelationsStable (r : G →* L) (s : L →* G) (θ : r.ker →* Rˣ)
    (hθ : ∀ l n, θ (inverseSectionConjugate r s l n) = θ n)
    (ρ : Representation R G V) (l : L) :
    Jacquet.Localization.relations ρ r.ker θ ≤
      (Jacquet.Localization.relations ρ r.ker θ).comap (ρ (s l)) := by
  apply Submodule.span_le.2
  rintro _ ⟨⟨n, v⟩, rfl⟩
  change ρ (s l) (ρ n v - (θ n : R) • v) ∈ Jacquet.Localization.relations ρ r.ker θ
  have h := Jacquet.Localization.sub_mem_relations ρ r.ker θ
    (inverseSectionConjugate r s l⁻¹ n) (ρ (s l) v)
  rw [hθ] at h
  simpa [inverseSectionConjugate] using h

/-- The unnormalized section action, on exactly the existing localized quotient. -/
def sectionAction (r : G →* L) (s : L →* G) (θ : r.ker →* Rˣ)
    (hθ : ∀ l n, θ (inverseSectionConjugate r s l n) = θ n)
    (ρ : Representation R G V) :
    Representation R L (Jacquet.Localization.Coinvariants ρ r.ker θ) :=
  Representation.quotient (ρ.comp s) (Jacquet.Localization.relations ρ r.ker θ)
    (sectionRelationsStable r s θ hθ ρ)

@[simp] theorem sectionAction_mk (r : G →* L) (s : L →* G) (θ : r.ker →* Rˣ)
    (hθ : ∀ l n, θ (inverseSectionConjugate r s l n) = θ n)
    (ρ : Representation R G V) (l : L) (v : V) :
    sectionAction r s θ hθ ρ l (Jacquet.Localization.mk ρ r.ker θ v) =
      Jacquet.Localization.mk ρ r.ker θ (ρ (s l) v) := rfl

/-- The quotient map intertwines restriction along the section and the new action. -/
def sectionQuotientMap (r : G →* L) (s : L →* G) (θ : r.ker →* Rˣ)
    (hθ : ∀ l n, θ (inverseSectionConjugate r s l n) = θ n)
    (ρ : Representation R G V) :
    Representation.IntertwiningMap (ρ.comp s) (sectionAction r s θ hθ ρ) where
  toLinearMap := Jacquet.Localization.mk ρ r.ker θ
  isIntertwining' _ := rfl

/-- Every intertwiner acts by its original linear map on quotient classes. -/
def sectionMap (r : G →* L) (s : L →* G) (θ : r.ker →* Rˣ)
    (hθ : ∀ l n, θ (inverseSectionConjugate r s l n) = θ n)
    {ρ : Representation R G V} {τ : Representation R G W} (f : ρ.IntertwiningMap τ) :
    (sectionAction r s θ hθ ρ).IntertwiningMap (sectionAction r s θ hθ τ) where
  toLinearMap := Jacquet.Localization.mapLinear r.ker θ f
  isIntertwining' l := by
    apply Jacquet.Localization.hom_ext
    ext v
    change Jacquet.Localization.mk τ r.ker θ (f (ρ (s l) v)) =
      Jacquet.Localization.mk τ r.ker θ (τ (s l) (f v))
    rw [Representation.IntertwiningMap.isIntertwining ρ τ f]

@[simp] theorem sectionMap_mk (r : G →* L) (s : L →* G) (θ : r.ker →* Rˣ)
    (hθ : ∀ l n, θ (inverseSectionConjugate r s l n) = θ n)
    {ρ : Representation R G V} {τ : Representation R G W}
    (f : ρ.IntertwiningMap τ) (v : V) :
    sectionMap r s θ hθ f (Jacquet.Localization.mk ρ r.ker θ v) =
      Jacquet.Localization.mk τ r.ker θ (f v) := rfl

@[simp] theorem sectionMap_id (r : G →* L) (s : L →* G) (θ : r.ker →* Rˣ)
    (hθ : ∀ l n, θ (inverseSectionConjugate r s l n) = θ n)
    (ρ : Representation R G V) :
    sectionMap r s θ hθ (Representation.IntertwiningMap.id ρ) =
      Representation.IntertwiningMap.id (sectionAction r s θ hθ ρ) := by
  apply Representation.IntertwiningMap.ext
  exact Jacquet.Localization.hom_ext rfl

@[simp] theorem sectionMap_comp (r : G →* L) (s : L →* G) (θ : r.ker →* Rˣ)
    (hθ : ∀ l n, θ (inverseSectionConjugate r s l n) = θ n)
    {ρ : Representation R G V} {τ : Representation R G W} {υ : Representation R G X}
    (f : ρ.IntertwiningMap τ) (g : τ.IntertwiningMap υ) :
    sectionMap r s θ hθ (g.comp f) =
      (sectionMap r s θ hθ g).comp (sectionMap r s θ hθ f) := by
  apply Representation.IntertwiningMap.ext
  exact Jacquet.Localization.hom_ext rfl

/-- Continuous restriction and a surjective quotient preserve smoothness. -/
theorem isSmooth_sectionAction [TopologicalSpace G] [TopologicalSpace L]
    (r : G →* L) (s : L →* G) (θ : r.ker →* Rˣ)
    (hθ : ∀ l n, θ (inverseSectionConjugate r s l n) = θ n)
    (ρ : Representation R G V) (hs : Continuous s) (hρ : IsSmooth ρ) :
    IsSmooth (sectionAction r s θ hθ ρ) :=
  isSmooth_of_surjective (sectionQuotientMap r s θ hθ ρ)
    (Jacquet.Localization.mk_surjective ρ r.ker θ) (isSmooth_comp s hs hρ)

/-- The ordinary kernel relations are stable under the section action. -/
theorem ordinarySectionRelationsStable (r : G →* L) (s : L →* G)
    (ρ : Representation R G V) (l : L) :
    Jacquet.relations ρ r.ker ≤ (Jacquet.relations ρ r.ker).comap (ρ (s l)) := by
  apply Submodule.span_le.2
  rintro _ ⟨⟨n, v⟩, rfl⟩
  change ρ (s l) (ρ n v - v) ∈ Jacquet.relations ρ r.ker
  have h := Jacquet.sub_mem_relations ρ r.ker
    (inverseSectionConjugate r s l⁻¹ n) (ρ (s l) v)
  simpa [inverseSectionConjugate] using h

/-- Ordinary kernel coinvariants, restricted along the section. -/
def ordinarySectionAction (r : G →* L) (s : L →* G) (ρ : Representation R G V) :
    Representation R L (Jacquet.Coinvariants ρ r.ker) :=
  Representation.quotient (ρ.comp s) (Jacquet.relations ρ r.ker)
    (ordinarySectionRelationsStable r s ρ)

@[simp] theorem ordinarySectionAction_mk (r : G →* L) (s : L →* G)
    (ρ : Representation R G V) (l : L) (v : V) :
    ordinarySectionAction r s ρ l (Jacquet.mk ρ r.ker v) =
      Jacquet.mk ρ r.ker (ρ (s l) v) := rfl

/-- The ordinary section quotient also sends an intertwiner to its class map. -/
def ordinarySectionMap (r : G →* L) (s : L →* G)
    {ρ : Representation R G V} {τ : Representation R G W} (f : ρ.IntertwiningMap τ) :
    (ordinarySectionAction r s ρ).IntertwiningMap (ordinarySectionAction r s τ) where
  toLinearMap := Representation.Coinvariants.map _ _ (Jacquet.restrictMap f r.ker)
  isIntertwining' l := by
    apply Representation.Coinvariants.hom_ext
    ext v
    change Jacquet.mk τ r.ker (f (ρ (s l) v)) = Jacquet.mk τ r.ker (τ (s l) (f v))
    rw [Representation.IntertwiningMap.isIntertwining ρ τ f]

@[simp] theorem ordinarySectionMap_mk (r : G →* L) (s : L →* G)
    {ρ : Representation R G V} {τ : Representation R G W}
    (f : ρ.IntertwiningMap τ) (v : V) :
    ordinarySectionMap r s f (Jacquet.mk ρ r.ker v) = Jacquet.mk τ r.ker (f v) := rfl

/-- Rescaling each generator by a unit identifies character and twisted ordinary relations. -/
theorem relations_eq_twisted (r : G →* L) (θ : r.ker →* Rˣ) (χ : G →* Rˣ)
    (hχ : ∀ n : r.ker, χ n = θ n) (ρ : Representation R G V) :
    Jacquet.Localization.relations ρ r.ker θ =
      Jacquet.relations (twist χ⁻¹ ρ) r.ker := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨⟨n, v⟩, rfl⟩
    have h := (Jacquet.relations (twist χ⁻¹ ρ) r.ker).smul_mem (θ n : R)
      (Jacquet.sub_mem_relations (twist χ⁻¹ ρ) r.ker n v)
    simpa [twist, smul_sub, smul_smul, hχ] using h
  · apply Submodule.span_le.2
    rintro _ ⟨⟨n, v⟩, rfl⟩
    have h := (Jacquet.Localization.relations ρ r.ker θ).smul_mem
      (((θ n)⁻¹ : Rˣ) : R) (Jacquet.Localization.sub_mem_relations ρ r.ker θ n v)
    simpa [twist, smul_sub, smul_smul, hχ] using h

/-- Identity on representatives, equivariant for the two section actions. -/
def twistSectionEquiv (r : G →* L) (s : L →* G) (θ : r.ker →* Rˣ)
    (hθ : ∀ l n, θ (inverseSectionConjugate r s l n) = θ n)
    (χ : G →* Rˣ) (hχ : ∀ n : r.ker, χ n = θ n)
    (hχs : ∀ l, χ (s l) = 1) (ρ : Representation R G V) :
    (sectionAction r s θ hθ ρ).Equiv (ordinarySectionAction r s (twist χ⁻¹ ρ)) where
  toLinearEquiv := Submodule.quotEquivOfEq _ _ (relations_eq_twisted r θ χ hχ ρ)
  isIntertwining' l := by
    apply Jacquet.Localization.hom_ext
    ext v
    change Jacquet.mk (twist χ⁻¹ ρ) r.ker (ρ (s l) v) =
      Jacquet.mk (twist χ⁻¹ ρ) r.ker (twist χ⁻¹ ρ (s l) v)
    simp [twist, hχs]

@[simp] theorem twistSectionEquiv_mk (r : G →* L) (s : L →* G) (θ : r.ker →* Rˣ)
    (hθ : ∀ l n, θ (inverseSectionConjugate r s l n) = θ n)
    (χ : G →* Rˣ) (hχ : ∀ n : r.ker, χ n = θ n)
    (hχs : ∀ l, χ (s l) = 1) (ρ : Representation R G V) (v : V) :
    twistSectionEquiv r s θ hθ χ hχ hχs ρ (Jacquet.Localization.mk ρ r.ker θ v) =
      Jacquet.mk (twist χ⁻¹ ρ) r.ker v := rfl

/-- The class-preserving equivalence is natural across independent carrier universes. -/
theorem twistSectionEquiv_natural (r : G →* L) (s : L →* G) (θ : r.ker →* Rˣ)
    (hθ : ∀ l n, θ (inverseSectionConjugate r s l n) = θ n)
    (χ : G →* Rˣ) (hχ : ∀ n : r.ker, χ n = θ n) (hχs : ∀ l, χ (s l) = 1)
    {ρ : Representation R G V} {τ : Representation R G W} (f : ρ.IntertwiningMap τ) :
    (ordinarySectionMap r s (twistIntertwining χ⁻¹ f)).comp
        (twistSectionEquiv r s θ hθ χ hχ hχs ρ).toIntertwiningMap =
      (twistSectionEquiv r s θ hθ χ hχ hχs τ).toIntertwiningMap.comp
        (sectionMap r s θ hθ f) := by
  apply Representation.IntertwiningMap.ext
  exact Jacquet.Localization.hom_ext rfl

end Langlands.Induction.SplitKernelLocalization
