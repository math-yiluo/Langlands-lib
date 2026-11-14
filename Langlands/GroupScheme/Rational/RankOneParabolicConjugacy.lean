import Langlands.GroupScheme.Rational.StandardParabolicClassificationProof
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof
import Langlands.GroupScheme.Rational.ParabolicNormalizerProof
import Langlands.GroupScheme.Rational.ParabolicConjugacyTransport
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport

/-! # Conjugates of the minimal standard parabolic inside a parabolic, and rank one -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A rational point whose inner automorphism has preimage `F` normalizes `F`. -/
theorem SubgroupFunctor.mem_normalizer_of_comap_innerIso_eq
    {F : SubgroupFunctor G} (h : GroupScheme.rationalPoints G)
    (hF : F.comap (G.innerIso h).hom = F) :
    h ∈ F.normalizer.rationalPoints := by
  have hF' : F.comap (G.innerIso h).inv = F := by
    conv_lhs => rw [← hF]
    exact SubgroupFunctor.comap_iso_hom_inv F (G.innerIso h)
  intro V a x hx
  have ha : a ≫ h = G.constantPoint h V := by
    rw [← G.constantPoint_naturality h a, constantPoint_rationalPoint]
  rw [ha]
  constructor
  · have hx' : x ∈ (F.comap (G.innerIso h).hom).carrier V := by rw [hF]; exact hx
    rw [SubgroupFunctor.mem_comap, comp_innerIso_hom] at hx'
    exact hx'
  · have hx' : x ∈ (F.comap (G.innerIso h).inv).carrier V := by rw [hF']; exact hx
    rw [SubgroupFunctor.mem_comap, ← G.innerIso_inv_hom, comp_innerIso_hom,
      constantPoint_inv, inv_inv] at hx'
    exact hx'

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- **Parabolics containing two conjugates of the minimal parabolic.** Let `i` be a maximal
split torus, `ν` a generic cocharacter and `P₀ = P(ν)` the corresponding minimal parabolic.
If a parabolic subgroup `j : P ⟶ G` contains `P₀` and also `Int(h)⁻¹`-preimage-contains
`P₀`, i.e. `h P₀ h⁻¹ ⊆ P`, then `h ∈ P(k)`. -/
theorem mem_rationalPoints_of_minimalParabolic_le_comap
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T)
    (hν : haveI := hG.isAffineHom; IsGenericCocharacter i ν)
    {P : GroupScheme (Spec (CommRingCat.of k))} (j : P ⟶ G) (hj : IsParabolicSubgroup j)
    (h0 : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤ SubgroupFunctor.range j)
    (h : GroupScheme.rationalPoints G)
    (hh : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
      (SubgroupFunctor.range j).comap (G.innerIso h).hom) :
    h ∈ (SubgroupFunctor.range j).rationalPoints := by
  have := hG.isAffineHom
  obtain ⟨χ, hχ⟩ := (parabolicDynamic k G hG P j hj.isClosedSubgroup).mp hj
  set χ' := χ ≫ (G.innerIso h).inv with hχ'def
  have hχ' : Dynamic.parabolic χ' = (Dynamic.parabolic χ).comap (G.innerIso h).hom := by
    have := Dynamic.parabolic_eq_comap_of_iso χ' (G.innerIso h)
    rwa [hχ'def, Category.assoc, Iso.inv_hom_id, Category.comp_id] at this
  have hcl := standardParabolicClassification k G hG T i hi ν hν
  obtain ⟨J₁, hJ₁, heJ₁⟩ := hcl.1 χ (by rw [← hχ]; exact h0)
  obtain ⟨J₂, hJ₂, heJ₂⟩ := hcl.1 χ' (by rw [hχ', ← hχ]; exact hh)
  obtain ⟨J, -, huniq⟩ := hcl.2 χ'
  have e₁ : (⟨J₁, hJ₁⟩ : {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν}) = J :=
    huniq ⟨J₁, hJ₁⟩ ⟨h, by rw [hχ', heJ₁]⟩
  have e₂ : (⟨J₂, hJ₂⟩ : {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν}) = J :=
    huniq ⟨J₂, hJ₂⟩ ⟨1, by rw [heJ₂, innerIso_one_hom, SubgroupFunctor.comap_id]⟩
  have hJ : J₁ = J₂ := congrArg Subtype.val (e₁.trans e₂.symm)
  have hcomap : (SubgroupFunctor.range j).comap (G.innerIso h).hom =
      SubgroupFunctor.range j := by
    rw [hχ, ← hχ', heJ₂, heJ₁, hJ]
  have hn := SubgroupFunctor.mem_normalizer_of_comap_innerIso_eq h hcomap
  rwa [parabolicSelfNormalizer k G hG P j hj] at hn

/-- **Coset form.** If a parabolic `j : P ⟶ G` contains both `m P₀ m⁻¹` and `h P₀ h⁻¹`,
where `P₀ = P(ν)` is the minimal parabolic of a maximal split torus and a generic
cocharacter, then `h ∈ P(k) · m`. -/
theorem exists_mul_eq_of_minimalParabolic_le_comap
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T)
    (hν : haveI := hG.isAffineHom; IsGenericCocharacter i ν)
    {P : GroupScheme (Spec (CommRingCat.of k))} (j : P ⟶ G) (hj : IsParabolicSubgroup j)
    (m h : GroupScheme.rationalPoints G)
    (hm : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
      (SubgroupFunctor.range j).comap (G.innerIso m).hom)
    (hh : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
      (SubgroupFunctor.range j).comap (G.innerIso h).hom) :
    ∃ p ∈ (SubgroupFunctor.range j).rationalPoints, h = p * m := by
  -- conjugate `j` back by `m`
  let j' : P ⟶ G := j ≫ (G.innerIso m).inv
  have hrange : SubgroupFunctor.range j' =
      (SubgroupFunctor.range j).comap (G.innerIso m).hom := by
    ext V x
    rw [SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y, ?_⟩
      simp only [j', Grp.comp_hom_hom, Category.assoc]
      rw [← Grp.comp_hom_hom (G.innerIso m).inv, Iso.inv_hom_id, Grp.id_hom_hom,
        Category.comp_id]
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      simp only [j', Grp.comp_hom_hom, ← Category.assoc, hy]
      rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom,
        Category.comp_id]
  have hj' : IsParabolicSubgroup j' := hj.comp_iso (G.innerIso m).symm
  have h0 : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤ SubgroupFunctor.range j' := by
    rw [hrange]; exact hm
  have hh' : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
      (SubgroupFunctor.range j').comap (G.innerIso (m⁻¹ * h)).hom := by
    rw [hrange, innerIso_mul_hom, ← SubgroupFunctor.comap_comp, Category.assoc,
      innerIso_inv_hom, Iso.inv_hom_id, Category.comp_id]
    exact hh
  have hmem := mem_rationalPoints_of_minimalParabolic_le_comap hG i hi ν hν j' hj' h0
    (m⁻¹ * h) hh'
  rw [hrange, SubgroupFunctor.mem_rationalPoints_comap_innerIso_hom] at hmem
  refine ⟨m * (m⁻¹ * h) * m⁻¹, hmem, ?_⟩
  group

/-- **Rank-one conjugacy.** If the simple relative roots of a maximal split torus `i` and
a generic cocharacter `ν` form a singleton, then every proper parabolic subgroup
(range different from everything) is rationally conjugate to the minimal standard
parabolic, in the classification convention `x ∈ Q ↔ g x g⁻¹ ∈ P_∅`. -/
theorem exists_range_eq_comap_standardParabolic_empty_of_rankOne
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T)
    (hν : haveI := hG.isAffineHom; IsGenericCocharacter i ν)
    (α : characterLattice T)
    (hα : haveI := hG.isAffineHom; simpleRelativeRoots i ν = {α})
    {Q : GroupScheme (Spec (CommRingCat.of k))} (jQ : Q ⟶ G) (hQ : IsParabolicSubgroup jQ)
    (hne : SubgroupFunctor.range jQ ≠ ⊤) :
    haveI := hG.isAffineHom
    ∃ g : GroupScheme.rationalPoints G,
      SubgroupFunctor.range jQ = (standardParabolic i ν ∅).comap (G.innerIso g).hom := by
  have := hG.isAffineHom
  obtain ⟨χ, hχ⟩ := (parabolicDynamic k G hG Q jQ hQ.isClosedSubgroup).mp hQ
  obtain ⟨⟨J, hJ⟩, ⟨g, hg⟩, -⟩ := (standardParabolicClassification k G hG T i hi ν hν).2 χ
  rw [hα, Set.subset_singleton_iff_eq] at hJ
  rcases hJ with rfl | rfl
  · exact ⟨g, hχ.trans hg⟩
  · exfalso
    have htop : standardParabolic i ν ({α} : Set (characterLattice T)) = ⊤ := by
      rw [← hα]
      exact (standardParabolicEndpoints k G hG T i hi ν hν).2.2.1
    apply hne
    rw [hχ, hg]
    change (standardParabolic i ν ({α} : Set (characterLattice T))).comap _ = ⊤
    rw [htop, SubgroupFunctor.comap_top]

end Langlands.GroupScheme
