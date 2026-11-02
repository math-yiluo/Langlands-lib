import Langlands.GroupScheme.Rational.RelativeRoots

/-! # Standard rational parabolic subgroup functors

Positivity is specified by a cocharacter. Standard subgroup functors are defined as
pointwise intersections over the cocharacters with the specified simple-root signs.
Their agreement with any one such cocharacter is a separate structural statement.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

section Roots

variable [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Relative roots that pair positively with the specified cocharacter. -/
def positiveRelativeRoots : Set (characterLattice T) :=
  {α | α ∈ relativeRoots i ∧ 0 < latticePairing T α ν}

/-- Positive relative roots that are not sums of two positive relative roots.
The definition uses all relative roots, including a possibly nonreduced system. -/
def simpleRelativeRoots : Set (characterLattice T) :=
  {α | α ∈ positiveRelativeRoots i ν ∧
    ¬ ∃ β ∈ positiveRelativeRoots i ν, ∃ γ ∈ positiveRelativeRoots i ν, α = β + γ}

theorem simpleRelativeRoots_subset_positive :
    simpleRelativeRoots i ν ⊆ positiveRelativeRoots i ν :=
  fun _ hα => hα.1

theorem positiveRelativeRoots_subset_relativeRoots :
    positiveRelativeRoots i ν ⊆ relativeRoots i :=
  fun _ hα => hα.1

/-- A standard cocharacter for `J` vanishes on `J` and is positive on the remaining
simple roots. The subset condition is included, so nonstandard indices have no witnesses. -/
def IsStandardCocharacter (J : Set (characterLattice T)) (zeta : cocharacterLattice T) : Prop :=
  J ⊆ simpleRelativeRoots i ν ∧
    (∀ α ∈ J, latticePairing T α zeta = 0) ∧
    ∀ α ∈ simpleRelativeRoots i ν, α ∉ J → 0 < latticePairing T α zeta

theorem IsStandardCocharacter.subset {J : Set (characterLattice T)}
    {zeta : cocharacterLattice T} (hzeta : IsStandardCocharacter i ν J zeta) :
    J ⊆ simpleRelativeRoots i ν :=
  hzeta.1

/-- Choice-free standard rational parabolic: the intersection over all standard
cocharacters for `J` of their dynamic parabolic subgroup functors. -/
def standardParabolic (J : Set (characterLattice T)) : SubgroupFunctor G where
  carrier U := ⨅ (zeta : cocharacterLattice T) (_ : IsStandardCocharacter i ν J zeta),
    (Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i)).carrier U
  comp_mem a _ hx := by
    simp only [Subgroup.mem_iInf] at hx ⊢
    intro zeta hzeta
    exact (Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i)).comp_mem a (hx zeta hzeta)

/-- Choice-free standard Levi: the intersection of the dynamic centralizers of
all standard cocharacters for `J`. -/
def standardLevi (J : Set (characterLattice T)) : SubgroupFunctor G where
  carrier U := ⨅ (zeta : cocharacterLattice T) (_ : IsStandardCocharacter i ν J zeta),
    (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).carrier U
  comp_mem a _ hx := by
    simp only [Subgroup.mem_iInf] at hx ⊢
    intro zeta hzeta
    exact (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).comp_mem a (hx zeta hzeta)

/-- Choice-free standard unipotent subgroup: the intersection of the dynamic
unipotent subgroup functors of all standard cocharacters for `J`. -/
def standardUnipotent (J : Set (characterLattice T)) : SubgroupFunctor G where
  carrier U := ⨅ (zeta : cocharacterLattice T) (_ : IsStandardCocharacter i ν J zeta),
    (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).carrier U
  comp_mem a _ hx := by
    simp only [Subgroup.mem_iInf] at hx ⊢
    intro zeta hzeta
    exact (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).comp_mem a (hx zeta hzeta)

theorem mem_standardParabolic {J : Set (characterLattice T)}
    {U : Over (Spec (CommRingCat.of k))} {g : U ⟶ G.X} :
    g ∈ (standardParabolic i ν J).carrier U ↔
      ∀ zeta, IsStandardCocharacter i ν J zeta →
        g ∈ (Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i)).carrier U := by
  simp only [standardParabolic, Subgroup.mem_iInf]

theorem mem_standardLevi {J : Set (characterLattice T)}
    {U : Over (Spec (CommRingCat.of k))} {g : U ⟶ G.X} :
    g ∈ (standardLevi i ν J).carrier U ↔
      ∀ zeta, IsStandardCocharacter i ν J zeta →
        g ∈ (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).carrier U := by
  simp only [standardLevi, Subgroup.mem_iInf]

theorem mem_standardUnipotent {J : Set (characterLattice T)}
    {U : Over (Spec (CommRingCat.of k))} {g : U ⟶ G.X} :
    g ∈ (standardUnipotent i ν J).carrier U ↔
      ∀ zeta, IsStandardCocharacter i ν J zeta →
        g ∈ (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).carrier U := by
  simp only [standardUnipotent, Subgroup.mem_iInf]

theorem standardLevi_le_standardParabolic (J : Set (characterLattice T)) :
    standardLevi i ν J ≤ standardParabolic i ν J := by
  intro U g hg
  rw [mem_standardLevi] at hg
  rw [mem_standardParabolic]
  intro zeta hzeta
  exact Dynamic.centralizer_le_parabolic _ U (hg zeta hzeta)

theorem standardUnipotent_le_standardParabolic (J : Set (characterLattice T)) :
    standardUnipotent i ν J ≤ standardParabolic i ν J := by
  intro U g hg
  rw [mem_standardUnipotent] at hg
  rw [mem_standardParabolic]
  intro zeta hzeta
  exact Dynamic.unipotent_le_parabolic _ U (hg zeta hzeta)

theorem torusCentralizer_le_standardLevi (J : Set (characterLattice T)) :
    torusCentralizer i ≤ standardLevi i ν J := by
  intro U g hg
  rw [mem_standardLevi]
  intro zeta _
  exact torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom zeta) U hg

theorem standardParabolic_le_dynamicParabolic {J : Set (characterLattice T)}
    {zeta : cocharacterLattice T} (hzeta : IsStandardCocharacter i ν J zeta) :
    standardParabolic i ν J ≤ Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) :=
  fun _ _ hg => (mem_standardParabolic i ν).1 hg zeta hzeta

theorem standardLevi_le_dynamicCentralizer {J : Set (characterLattice T)}
    {zeta : cocharacterLattice T} (hzeta : IsStandardCocharacter i ν J zeta) :
    standardLevi i ν J ≤ Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) :=
  fun _ _ hg => (mem_standardLevi i ν).1 hg zeta hzeta

theorem standardUnipotent_le_dynamicUnipotent {J : Set (characterLattice T)}
    {zeta : cocharacterLattice T} (hzeta : IsStandardCocharacter i ν J zeta) :
    standardUnipotent i ν J ≤ Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) :=
  fun _ _ hg => (mem_standardUnipotent i ν).1 hg zeta hzeta

/-- Rational points of the standard parabolic, as a subgroup of the actual `G(k)`. -/
abbrev standardParabolicPoints (J : Set (characterLattice T)) :
    Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :=
  (standardParabolic i ν J).carrier (Over.mk (𝟙 _))

/-- Rational points of the standard Levi, as a subgroup of the actual `G(k)`. -/
abbrev standardLeviPoints (J : Set (characterLattice T)) :
    Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :=
  (standardLevi i ν J).carrier (Over.mk (𝟙 _))

/-- Rational points of the standard unipotent subgroup, inside the actual `G(k)`. -/
abbrev standardUnipotentPoints (J : Set (characterLattice T)) :
    Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :=
  (standardUnipotent i ν J).carrier (Over.mk (𝟙 _))

/-- The subgroup of the relative Weyl group represented by normalizing points in
the standard Levi. This is the image of an actual subgroup of normalizer points. -/
def standardRelativeWeylGroup (J : Set (characterLattice T)) :
    Subgroup (relativeWeylGroup i) :=
  ((standardLeviPoints i ν J).subgroupOf (normalizerPoints i)).map
    (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)))

theorem mem_standardRelativeWeylGroup_iff {J : Set (characterLattice T)}
    {w : relativeWeylGroup i} :
    w ∈ standardRelativeWeylGroup i ν J ↔
      ∃ n : normalizerPoints i,
        (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ∈ standardLeviPoints i ν J ∧
        QuotientGroup.mk n = w :=
  Iff.rfl

end Roots

end Langlands.GroupScheme
