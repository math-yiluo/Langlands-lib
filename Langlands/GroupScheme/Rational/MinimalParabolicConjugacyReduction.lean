import Langlands.GroupScheme.Rational.MinimalParabolicStatement
import Langlands.GroupScheme.Rational.ParabolicConjugacyTransport
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Dynamic.AffineRepresentability

/-! # Moving a rational parabolic above a fixed minimal parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {H H' G G' : GroupScheme S}

/-- An isomorphism square for subgroup presentations gives equality of their
all-test ranges in the preimage convention. No monicity is needed. -/
theorem range_eq_comap_of_iso_square {i : H ⟶ G} {i' : H' ⟶ G'}
    (e : G ≅ G') (d : H ≅ H') (h : i ≫ e.hom = d.hom ≫ i') :
    range i = (range i').comap e.hom := by
  have he : i.hom.hom ≫ e.hom.hom.hom = d.hom.hom.hom ≫ i'.hom.hom :=
    congrArg (fun f : H ⟶ G' => f.hom.hom) h
  have hd : d.inv.hom.hom ≫ d.hom.hom.hom = 𝟙 H'.X :=
    congrArg (fun f : H' ⟶ H' => f.hom.hom) d.inv_hom_id
  have : IsIso e.hom.hom.hom :=
    (inferInstance : IsIso ((Grp.forget _).mapIso e).hom)
  apply ext
  intro U
  apply Subgroup.ext
  intro x
  rw [mem_comap, mem_range, mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y ≫ d.hom.hom.hom, ?_⟩
    rw [Category.assoc, ← he, ← Category.assoc]
  · rintro ⟨y, hy⟩
    refine ⟨y ≫ d.inv.hom.hom, ?_⟩
    apply (cancel_mono e.hom.hom.hom).mp
    calc
      ((y ≫ d.inv.hom.hom) ≫ i.hom.hom) ≫ e.hom.hom.hom =
          y ≫ d.inv.hom.hom ≫ (i.hom.hom ≫ e.hom.hom.hom) := by
            simp only [Category.assoc]
      _ = y ≫ d.inv.hom.hom ≫ (d.hom.hom.hom ≫ i'.hom.hom) := by rw [he]
      _ = y ≫ i'.hom.hom := by
        rw [← Category.assoc d.inv.hom.hom, hd, Category.id_comp]
      _ = x ≫ e.hom.hom.hom := hy

end SubgroupFunctor

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Actual minimal-parabolic conjugacy implies rational conjugacy of their
subgroup functors, with equality on every test scheme. -/
theorem IsMinimalParabolicFunctor.isRationallyConjugate_of_statement
    (hconj : MinimalParabolicConjugacyStatement.{u}) (hG : IsConnectedReductive G)
    {M M' : SubgroupFunctor G} (hM : IsMinimalParabolicFunctor M)
    (hM' : IsMinimalParabolicFunctor M') :
    M.IsRationallyConjugate M' := by
  obtain ⟨P, j, hj, heq⟩ := isMinimalParabolicFunctor_iff_exists.mp hM
  obtain ⟨P', j', hj', heq'⟩ := isMinimalParabolicFunctor_iff_exists.mp hM'
  obtain ⟨g, e, he⟩ := hconj k G hG P P' j j' hj hj'
  refine ⟨g, ?_⟩
  rw [← heq, ← heq']
  exact SubgroupFunctor.range_eq_comap_of_iso_square (G.innerIso g) e he

/-- The actual minimal-containment statement supplies a minimal subgroup functor
inside a given parabolic functor. -/
theorem IsParabolicFunctor.exists_minimal_le_of_statement
    (hcontains : ParabolicContainsMinimalStatement.{u}) (hG : IsConnectedReductive G)
    {F : SubgroupFunctor G} (hF : IsParabolicFunctor F) :
    ∃ M : SubgroupFunctor G, IsMinimalParabolicFunctor M ∧ M ≤ F := by
  obtain ⟨P, j, hj, heq⟩ := hF
  obtain ⟨Q, j', hj', hle⟩ := hcontains k G hG P j hj
  exact ⟨SubgroupFunctor.range j', hj'.isMinimalParabolicFunctor, heq ▸ hle⟩

/-- Minimal containment and rational conjugacy move any parabolic functor above
a fixed minimal one. The inverse of `Int(g)` has the forward-image orientation. -/
theorem exists_conjugate_containing_minimal_of_statements
    (hconj : MinimalParabolicConjugacyStatement.{u})
    (hcontains : ParabolicContainsMinimalStatement.{u}) (hG : IsConnectedReductive G)
    {M F : SubgroupFunctor G} (hM : IsMinimalParabolicFunctor M)
    (hF : IsParabolicFunctor F) :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      M ≤ F.comap (G.innerIso g).inv := by
  obtain ⟨M', hM', hle⟩ := hF.exists_minimal_le_of_statement hcontains hG
  obtain ⟨g, hg⟩ := hM'.isRationallyConjugate_of_statement hconj hG hM
  refine ⟨g, ?_⟩
  have h := SubgroupFunctor.comap_mono (f := (G.innerIso g).inv) hle
  rwa [hg, SubgroupFunctor.comap_iso_hom_inv] at h

/-- A rational point whose conjugate of `F` contains the fixed minimal `M`,
bundled with its all-test containment certificate. -/
def conjugatingPointContainingMinimal_of_statements
    (hconj : MinimalParabolicConjugacyStatement.{u})
    (hcontains : ParabolicContainsMinimalStatement.{u}) (hG : IsConnectedReductive G)
    {M F : SubgroupFunctor G} (hM : IsMinimalParabolicFunctor M)
    (hF : IsParabolicFunctor F) :
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X //
      M ≤ F.comap (G.innerIso g).inv} :=
  Classical.indefiniteDescription _
    (exists_conjugate_containing_minimal_of_statements hconj hcontains hG hM hF)

set_option maxHeartbeats 800000 in
/-- Conditional all-test reduction of rational conjugacy existence to the four
published structural statements. It covers every cocharacter. -/
theorem exists_conjugate_dynamicParabolic_containing_generic_of_minimal_statements
    (hdynamic : ParabolicDynamicStatement.{u})
    (hgeneric : GenericMinimalParabolicStatement.{u})
    (hconj : MinimalParabolicConjugacyStatement.{u})
    (hcontains : ParabolicContainsMinimalStatement.{u})
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) :
    letI := hG.isAffineHom
    IsGenericCocharacter i ν →
      ∀ zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
        ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
          Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
            Dynamic.parabolic (zeta ≫ (G.innerIso g).hom) := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro hν zeta
  have hrep := Dynamic.Affine.isRepresentedBy_parabolicHom zeta
  have hclosed := Dynamic.Affine.isClosedSubgroup_parabolicHom zeta
  have hparabolic : IsParabolicSubgroup (Dynamic.Affine.parabolicHom zeta) :=
    (hdynamic k G hG _ _ hclosed).mpr ⟨zeta, hrep.2⟩
  have hF : IsParabolicFunctor (Dynamic.parabolic zeta) :=
    ⟨_, _, hparabolic, hrep.2⟩
  obtain ⟨g, hg⟩ := exists_conjugate_containing_minimal_of_statements hconj hcontains hG
    (hgeneric k G hG T i hi ν hν) hF
  refine ⟨g, ?_⟩
  have he := (SubgroupFunctor.eq_comap_iso_iff (G.innerIso g)).mp
    (Dynamic.parabolic_eq_comap_of_iso zeta (G.innerIso g))
  rwa [he] at hg

end Langlands.GroupScheme
