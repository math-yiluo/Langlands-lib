import Langlands.Representation.Induction.SplitKernelCharacterExtension
import Langlands.Representation.Induction.SplitKernelSectionAction

/-! Concrete split-kernel character localization and subgroup intersection data. -/

noncomputable section

namespace Langlands.Induction.SplitKernelLocalization

universe uG uL uV uW uX

variable {G : Type uG} {L : Type uL} [Group G] [Group L]
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup X] [Module ℂ X]

/-- The exact localized quotient with its unnormalized section action. -/
abbrev localizedAction (r : G →* L) (s : L →* G) (θ : r.ker →* ℂˣ)
    (hθ : SectionInvariant r s θ) (ρ : Representation ℂ G V) :
    Representation ℂ L (Jacquet.Localization.Coinvariants ρ r.ker θ) :=
  sectionAction r s θ hθ ρ

@[simp] theorem localizedAction_mk (r : G →* L) (s : L →* G) (θ : r.ker →* ℂˣ)
    (hθ : SectionInvariant r s θ) (ρ : Representation ℂ G V) (l : L) (v : V) :
    localizedAction r s θ hθ ρ l (Jacquet.Localization.mk ρ r.ker θ v) =
      Jacquet.Localization.mk ρ r.ker θ (ρ (s l) v) := rfl

/-- The requested comparison uses the constructed character extension itself. -/
def extensionTwistEquiv (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (θ : r.ker →* ℂˣ) (hθ : SectionInvariant r s θ) (ρ : Representation ℂ G V) :
    (localizedAction r s θ hθ ρ).Equiv
      (ordinarySectionAction r s (twist (characterExtension r s hrs θ hθ)⁻¹ ρ)) :=
  twistSectionEquiv r s θ hθ (characterExtension r s hrs θ hθ)
    (characterExtension_kernel r s hrs θ hθ) (characterExtension_section r s hrs θ hθ) ρ

@[simp] theorem extensionTwistEquiv_mk (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (θ : r.ker →* ℂˣ) (hθ : SectionInvariant r s θ)
    (ρ : Representation ℂ G V) (v : V) :
    extensionTwistEquiv r s hrs θ hθ ρ (Jacquet.Localization.mk ρ r.ker θ v) =
      Jacquet.mk (twist (characterExtension r s hrs θ hθ)⁻¹ ρ) r.ker v := rfl

/-- Naturality holds for every ambient intertwiner, with independent carriers. -/
theorem extensionTwistEquiv_natural (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (θ : r.ker →* ℂˣ) (hθ : SectionInvariant r s θ)
    {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (f : ρ.IntertwiningMap τ) :
    (ordinarySectionMap r s (twistIntertwining (characterExtension r s hrs θ hθ)⁻¹ f)).comp
        (extensionTwistEquiv r s hrs θ hθ ρ).toIntertwiningMap =
      (extensionTwistEquiv r s hrs θ hθ τ).toIntertwiningMap.comp (sectionMap r s θ hθ f) :=
  twistSectionEquiv_natural r s θ hθ (characterExtension r s hrs θ hθ)
    (characterExtension_kernel r s hrs θ hθ) (characterExtension_section r s hrs θ hθ) f

/-- Restriction of the retraction to the actual subgroup. -/
def subgroupRetraction (r : G →* L) (H : Subgroup G) : H →* L := r.comp H.subtype

/-- The actual section element belongs to `H` by the supplied containment proof. -/
def subgroupSection (s : L →* G) (H : Subgroup G) (hsH : ∀ l, s l ∈ H) : L →* H where
  toFun l := ⟨s l, hsH l⟩
  map_one' := Subtype.ext (map_one s)
  map_mul' l m := Subtype.ext (map_mul s l m)

@[simp] theorem subgroupSection_val (s : L →* G) (H : Subgroup G)
    (hsH : ∀ l, s l ∈ H) (l : L) : (subgroupSection s H hsH l : G) = s l := rfl

@[simp] theorem subgroupRetraction_section (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (H : Subgroup G) (hsH : ∀ l, s l ∈ H) (l : L) :
    subgroupRetraction r H (subgroupSection s H hsH l) = l := hrs l

/-- The kernel intersection realized inside `H`, without a trivial-character condition. -/
def kernelIntersection (r : G →* L) (H : Subgroup G) : Subgroup H :=
  r.ker.comap H.subtype

@[simp] theorem kernelIntersection_eq_ker (r : G →* L) (H : Subgroup G) :
    kernelIntersection r H = (subgroupRetraction r H).ker := rfl

/-- The actual inclusion of the intersection into the kernel of `r`. -/
def intersectionToKernel (r : G →* L) (H : Subgroup G) : kernelIntersection r H →* r.ker where
  toFun n := ⟨((n : H) : G), n.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The restricted character, which may be nontrivial on the intersection. -/
def intersectionCharacter (r : G →* L) (θ : r.ker →* ℂˣ) (H : Subgroup G) :
    kernelIntersection r H →* ℂˣ := θ.comp (intersectionToKernel r H)

@[simp] theorem intersectionCharacter_apply (r : G →* L) (θ : r.ker →* ℂˣ)
    (H : Subgroup G) (n : kernelIntersection r H) :
    intersectionCharacter r θ H n = θ (intersectionToKernel r H n) := rfl

/-- Kernel-character invariance restricts to actual inverse conjugation inside `H`. -/
theorem subgroupInvariant (r : G →* L) (s : L →* G) (θ : r.ker →* ℂˣ)
    (hθ : SectionInvariant r s θ) (H : Subgroup G) (hsH : ∀ l, s l ∈ H) :
    SectionInvariant (subgroupRetraction r H) (subgroupSection s H hsH)
      (intersectionCharacter r θ H) := by
  intro l n
  exact hθ l (intersectionToKernel r H n)

/-- The concrete localized quotient of a representation of `H`, with its `L` action. -/
abbrev subgroupAction (r : G →* L) (s : L →* G) (θ : r.ker →* ℂˣ)
    (hθ : SectionInvariant r s θ) (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    (σ : Representation ℂ H V) :
    Representation ℂ L
      (Jacquet.Localization.Coinvariants σ (kernelIntersection r H) (intersectionCharacter r θ H)) :=
  sectionAction (subgroupRetraction r H) (subgroupSection s H hsH) (intersectionCharacter r θ H)
    (subgroupInvariant r s θ hθ H hsH) σ

@[simp] theorem subgroupAction_mk (r : G →* L) (s : L →* G) (θ : r.ker →* ℂˣ)
    (hθ : SectionInvariant r s θ) (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    (σ : Representation ℂ H V) (l : L) (v : V) :
    subgroupAction r s θ hθ H hsH σ l
        (Jacquet.Localization.mk σ (kernelIntersection r H) (intersectionCharacter r θ H) v) =
      Jacquet.Localization.mk σ (kernelIntersection r H) (intersectionCharacter r θ H)
        (σ (subgroupSection s H hsH l) v) := rfl

/-- The actual quotient class map for every intertwiner of `H` representations. -/
def subgroupMap (r : G →* L) (s : L →* G) (θ : r.ker →* ℂˣ)
    (hθ : SectionInvariant r s θ) (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    {σ : Representation ℂ H V} {τ : Representation ℂ H W} (f : σ.IntertwiningMap τ) :
    (subgroupAction r s θ hθ H hsH σ).IntertwiningMap (subgroupAction r s θ hθ H hsH τ) :=
  sectionMap (subgroupRetraction r H) (subgroupSection s H hsH) (intersectionCharacter r θ H)
    (subgroupInvariant r s θ hθ H hsH) f

@[simp] theorem subgroupMap_mk (r : G →* L) (s : L →* G) (θ : r.ker →* ℂˣ)
    (hθ : SectionInvariant r s θ) (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    {σ : Representation ℂ H V} {τ : Representation ℂ H W} (f : σ.IntertwiningMap τ) (v : V) :
    subgroupMap r s θ hθ H hsH f
        (Jacquet.Localization.mk σ (kernelIntersection r H) (intersectionCharacter r θ H) v) =
      Jacquet.Localization.mk τ (kernelIntersection r H) (intersectionCharacter r θ H) (f v) := rfl

@[simp] theorem subgroupMap_id (r : G →* L) (s : L →* G) (θ : r.ker →* ℂˣ)
    (hθ : SectionInvariant r s θ) (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    (σ : Representation ℂ H V) :
    subgroupMap r s θ hθ H hsH (Representation.IntertwiningMap.id σ) =
      Representation.IntertwiningMap.id (subgroupAction r s θ hθ H hsH σ) :=
  sectionMap_id (subgroupRetraction r H) (subgroupSection s H hsH) (intersectionCharacter r θ H)
    (subgroupInvariant r s θ hθ H hsH) σ

@[simp] theorem subgroupMap_comp (r : G →* L) (s : L →* G) (θ : r.ker →* ℂˣ)
    (hθ : SectionInvariant r s θ) (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    {σ : Representation ℂ H V} {τ : Representation ℂ H W} {υ : Representation ℂ H X}
    (f : σ.IntertwiningMap τ) (g : τ.IntertwiningMap υ) :
    subgroupMap r s θ hθ H hsH (g.comp f) =
      (subgroupMap r s θ hθ H hsH g).comp (subgroupMap r s θ hθ H hsH f) :=
  sectionMap_comp (subgroupRetraction r H) (subgroupSection s H hsH) (intersectionCharacter r θ H)
    (subgroupInvariant r s θ hθ H hsH) f g

/-- Smoothness of the actual subgroup quotient, with only continuity of the section. -/
theorem isSmooth_subgroupAction [TopologicalSpace G] [TopologicalSpace L]
    (r : G →* L) (s : L →* G) (θ : r.ker →* ℂˣ) (hθ : SectionInvariant r s θ)
    (H : Subgroup G) (hsH : ∀ l, s l ∈ H) (σ : Representation ℂ H V)
    (hs : Continuous s) (hσ : IsSmooth σ) : IsSmooth (subgroupAction r s θ hθ H hsH σ) :=
  isSmooth_sectionAction (subgroupRetraction r H) (subgroupSection s H hsH)
    (intersectionCharacter r θ H) (subgroupInvariant r s θ hθ H hsH) σ
    (hs.subtype_mk _) hσ

/-- Restriction of the constructed extension to `H`. -/
def restrictedExtension (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (θ : r.ker →* ℂˣ) (hθ : SectionInvariant r s θ) (H : Subgroup G) : H →* ℂˣ :=
  (characterExtension r s hrs θ hθ).comp H.subtype

@[simp] theorem restrictedExtension_intersection (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (θ : r.ker →* ℂˣ) (hθ : SectionInvariant r s θ)
    (H : Subgroup G) (n : kernelIntersection r H) :
    restrictedExtension r s hrs θ hθ H n = intersectionCharacter r θ H n :=
  characterExtension_kernel r s hrs θ hθ (intersectionToKernel r H n)

@[simp] theorem restrictedExtension_section (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (θ : r.ker →* ℂˣ) (hθ : SectionInvariant r s θ)
    (H : Subgroup G) (hsH : ∀ l, s l ∈ H) (l : L) :
    restrictedExtension r s hrs θ hθ H (subgroupSection s H hsH l) = 1 :=
  characterExtension_section r s hrs θ hθ l

/-- Identity on classes, retaining the actual `L` action on both intersection quotients. -/
def subgroupTwistEquiv (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (θ : r.ker →* ℂˣ) (hθ : SectionInvariant r s θ) (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    (σ : Representation ℂ H V) :
    (subgroupAction r s θ hθ H hsH σ).Equiv
      (ordinarySectionAction (subgroupRetraction r H) (subgroupSection s H hsH)
        (twist (((characterExtension r s hrs θ hθ)⁻¹).comp H.subtype) σ)) :=
  twistSectionEquiv (subgroupRetraction r H) (subgroupSection s H hsH)
    (intersectionCharacter r θ H) (subgroupInvariant r s θ hθ H hsH)
    (restrictedExtension r s hrs θ hθ H) (restrictedExtension_intersection r s hrs θ hθ H)
    (restrictedExtension_section r s hrs θ hθ H hsH) σ

@[simp] theorem subgroupTwistEquiv_mk (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (θ : r.ker →* ℂˣ) (hθ : SectionInvariant r s θ)
    (H : Subgroup G) (hsH : ∀ l, s l ∈ H) (σ : Representation ℂ H V) (v : V) :
    subgroupTwistEquiv r s hrs θ hθ H hsH σ
        (Jacquet.Localization.mk σ (kernelIntersection r H) (intersectionCharacter r θ H) v) =
      Jacquet.mk (twist (((characterExtension r s hrs θ hθ)⁻¹).comp H.subtype) σ)
        (kernelIntersection r H) v := rfl

/-- Naturality for arbitrary subgroup intertwiners, including all smooth intertwiners. -/
theorem subgroupTwistEquiv_natural (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (θ : r.ker →* ℂˣ) (hθ : SectionInvariant r s θ)
    (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    {σ : Representation ℂ H V} {τ : Representation ℂ H W} (f : σ.IntertwiningMap τ) :
    (ordinarySectionMap (subgroupRetraction r H) (subgroupSection s H hsH)
        (twistIntertwining (((characterExtension r s hrs θ hθ)⁻¹).comp H.subtype) f)).comp
        (subgroupTwistEquiv r s hrs θ hθ H hsH σ).toIntertwiningMap =
      (subgroupTwistEquiv r s hrs θ hθ H hsH τ).toIntertwiningMap.comp
        (subgroupMap r s θ hθ H hsH f) :=
  twistSectionEquiv_natural (subgroupRetraction r H) (subgroupSection s H hsH)
    (intersectionCharacter r θ H) (subgroupInvariant r s θ hθ H hsH)
    (restrictedExtension r s hrs θ hθ H) (restrictedExtension_intersection r s hrs θ hθ H)
    (restrictedExtension_section r s hrs θ hθ H hsH) f

/-- The other intersection realization, as a subgroup of the kernel. -/
def kernelSideIntersection (r : G →* L) (H : Subgroup G) : Subgroup r.ker :=
  H.comap r.ker.subtype

/-- Swap the two membership proofs; the ambient group element is unchanged. -/
def intersectionEquiv (r : G →* L) (H : Subgroup G) :
    kernelIntersection r H ≃* kernelSideIntersection r H where
  toFun n := ⟨⟨((n : H) : G), n.property⟩, (n : H).property⟩
  invFun n := ⟨⟨((n : r.ker) : G), n.property⟩, (n : r.ker).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The actual inclusion from `H.comap r.ker.subtype` to `H`. -/
def intersectionInclusion (r : G →* L) (H : Subgroup G) : kernelSideIntersection r H →* H where
  toFun n := ⟨((n : r.ker) : G), n.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The kernel-side restricted character points from the intersection to the units. -/
def kernelSideCharacter (r : G →* L) (θ : r.ker →* ℂˣ) (H : Subgroup G) :
    kernelSideIntersection r H →* ℂˣ := θ.comp (kernelSideIntersection r H).subtype

@[simp] theorem intersectionEquiv_character (r : G →* L) (θ : r.ker →* ℂˣ)
    (H : Subgroup G) (n : kernelIntersection r H) :
    intersectionCharacter r θ H n = kernelSideCharacter r θ H (intersectionEquiv r H n) := rfl

/-- The concrete equivalence to the whole localizing group inside the kernel-side intersection. -/
def intersectionTopEquiv (r : G →* L) (H : Subgroup G) :
    kernelIntersection r H ≃* (⊤ : Subgroup (kernelSideIntersection r H)) :=
  (intersectionEquiv r H).trans Subgroup.topEquiv.symm

/-- Canonical identification with localization of the restriction to `I` at all of `I`. -/
def intersectionWholeEquiv (r : G →* L) (θ : r.ker →* ℂˣ) (H : Subgroup G)
    (σ : Representation ℂ H V) :
    Jacquet.Localization.Coinvariants σ (kernelIntersection r H) (intersectionCharacter r θ H) ≃ₗ[ℂ]
      Jacquet.Localization.Coinvariants (σ.comp (intersectionInclusion r H))
        (⊤ : Subgroup (kernelSideIntersection r H))
        ((kernelSideCharacter r θ H).comp (⊤ : Subgroup (kernelSideIntersection r H)).subtype) :=
  Jacquet.Localization.transportEquiv σ (σ.comp (intersectionInclusion r H))
    (kernelIntersection r H) ⊤ (intersectionCharacter r θ H)
    ((kernelSideCharacter r θ H).comp (⊤ : Subgroup (kernelSideIntersection r H)).subtype)
    (intersectionTopEquiv r H) (LinearEquiv.refl ℂ V) (fun _ _ => rfl) (fun _ => rfl)

@[simp] theorem intersectionWholeEquiv_mk (r : G →* L) (θ : r.ker →* ℂˣ)
    (H : Subgroup G) (σ : Representation ℂ H V) (v : V) :
    intersectionWholeEquiv r θ H σ
        (Jacquet.Localization.mk σ (kernelIntersection r H) (intersectionCharacter r θ H) v) =
      Jacquet.Localization.mk (σ.comp (intersectionInclusion r H))
        (⊤ : Subgroup (kernelSideIntersection r H))
        ((kernelSideCharacter r θ H).comp (⊤ : Subgroup (kernelSideIntersection r H)).subtype) v := rfl

end Langlands.Induction.SplitKernelLocalization
