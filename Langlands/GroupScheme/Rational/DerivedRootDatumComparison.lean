import Langlands.GroupScheme.Rational.DerivedCorootReflection
import Langlands.GroupScheme.Rational.DerivedRelativeRoots
import Langlands.GroupScheme.Reductive.RootDatumSubgroupCoroots
import Langlands.GroupScheme.CentralIsogeny.RootDatumHomAssembly

/-! # Integral root data through the actual derived inclusion -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {T A S : CommGroupScheme (Spec (CommRingCat.of k))}
    {D G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom D.X.hom] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (e : T ⟶ S) (c : A ⟶ S) (j : T.toGrp ⟶ D) (i : S.toGrp ⟶ G)
    (d : D ⟶ G)
    (hsquare : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hT : IsSplitTorus T.toGrp) (hA : IsSplitTorus A.toGrp)
    [hpflat : Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    [hpsurj : Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ i))
    {J : Type v} {K : Type w}
    {P : RootDatum J (characterLattice S) (cocharacterLattice S)}
    {Q : RootDatum K (characterLattice T) (cocharacterLattice T)}

include hsquare hT hA hpflat hpsurj hc in
/-- Matching roots have compatible actual integral coroots through a central
complement, without requiring the retained torus map to be an epimorphism. -/
theorem IsRootDatumOf.coroot_comp_of_centralComplement
    [Mono i.hom.hom.left] [Finite (weylImage i)]
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf j Q)
    {p : J} {q : K} (hroot : e ≫ P.root p = Q.root q) :
    Q.coroot q ≫ e = P.coroot p := by
  have hz : c ≫ P.root p = 0 := by
    apply root_restrict_eq_zero_of_isCentral i c hA hc
    change P.root p ∈ roots i
    rw [← hP.2.1]
    exact ⟨p, rfl⟩
  obtain ⟨n, hn⟩ := hQ.exists_normalizing_latticeReflectionIso_of_centralComplement
    e c j i d hsquare hc hT q (P.root p) hroot hz
  exact hP.coroot_eq_of_normalizing_latticeReflectionIso i p rfl
    (Q.coroot q ≫ e) _ hn

variable [LocallyOfFiniteType D.X.hom] [Smooth G.X.hom]
    (hd : IsDerivedSubgroup d) (hS : IsSplitTorus S.toGrp)

omit [LocallyOfFiniteType G.X.hom] in
include hsquare hT hA hpflat hpsurj hc hd hS in
/-- Literal character restriction bijects the root ranges of supplied actual
root data under the derived inclusion and its central complement. -/
theorem IsRootDatumOf.bijOn_roots_precomp_derived
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf j Q) :
    Set.BijOn (fun α : characterLattice S => e ≫ α)
      (Set.range P.root) (Set.range Q.root) := by
  rw [hP.2.1, hQ.2.1]
  change Set.BijOn (fun α : characterLattice S => e ≫ α)
    (relativeRoots i) (relativeRoots j)
  refine ⟨?_, ?_, ?_⟩
  · intro α hα
    exact RelativeRoot.mem_relativeRoots_precomp_derived
      e c j i d hd hsquare hT hS hA hc hα
  · intro α hα β hβ hab
    exact RelativeRoot.precomp_injective_relativeRoots_derived e c i hA hc hα hβ hab
  · intro β hβ
    exact RelativeRoot.exists_relativeRoot_precomp_eq_derived
      e j i d hd hsquare hT hS hβ

/-- Actual character restriction and cocharacter pushforward form a morphism
of the supplied integral root data through the actual derived inclusion. -/
def IsRootDatumOf.derivedRootDatumHom
    [Mono i.hom.hom.left] [Finite (weylImage i)]
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf j Q) :
    RootPairing.Hom P Q :=
  RootDatumHom.ofRootCoroot Q P e hQ.1 hP.1
    (hP.bijOn_roots_precomp_derived e c j i d hsquare hT hA hc hd hS hQ)
    (fun _q _p hroot =>
      hP.coroot_comp_of_centralComplement e c j i d hsquare hT hA hc hQ hroot)

@[simp]
theorem IsRootDatumOf.derivedRootDatumHom_weightMap
    [Mono i.hom.hom.left] [Finite (weylImage i)]
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf j Q) (α : characterLattice S) :
    (hP.derivedRootDatumHom e c j i d hsquare hT hA hc hd hS hQ).weightMap α = e ≫ α :=
  rfl

@[simp]
theorem IsRootDatumOf.derivedRootDatumHom_coweightMap
    [Mono i.hom.hom.left] [Finite (weylImage i)]
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf j Q) (ν : cocharacterLattice T) :
    (hP.derivedRootDatumHom e c j i d hsquare hT hA hc hd hS hQ).coweightMap ν = ν ≫ e :=
  rfl

include hsquare hT hA hpflat hpsurj hc hd hS in
/-- The full integral derived coroot span maps onto the ambient integral
coroot span, under the supplied actual central complement and root data. -/
theorem IsRootDatumOf.map_corootSpan_derived
    [Mono i.hom.hom.left] [Finite (weylImage i)]
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf j Q) :
    (Q.corootSpan ℤ).map (RealTorusSpace.cocharacterMapInt e) = P.corootSpan ℤ := by
  let f := hP.derivedRootDatumHom e c j i d hsquare hT hA hc hd hS hQ
  change (Q.corootSpan ℤ).map f.coweightMap = P.corootSpan ℤ
  rw [RootPairing.corootSpan, Submodule.map_span]
  apply congrArg (Submodule.span ℤ)
  ext ν
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨f.indexEquiv.symm q, (f.coroot_coweightMap_apply P Q q).symm⟩
  · rintro ⟨p, rfl⟩
    refine ⟨Q.coroot (f.indexEquiv p), ⟨f.indexEquiv p, rfl⟩, ?_⟩
    simpa only [Equiv.symm_apply_apply] using f.coroot_coweightMap_apply P Q (f.indexEquiv p)

end Langlands.GroupScheme
