import Langlands.BruhatTits.IntegralModels.IntegralTorusCharacterNaturality
import Langlands.GroupScheme.Rational.QuasiSplitRootRestriction
import Langlands.GroupScheme.Rational.FiniteFieldQuasiSplit

/-! # Residue roots and nonzero generic torus restriction -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Extension

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {U : CommGroupScheme (Spec (CommRingCat.of L))}

private local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k L))
  infer_instance

private local instance : LocallyOfFiniteType
    ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k L))
  infer_instance

/-- A split maximal torus over an extension containing the original maximal
split torus has no root vanishing on that original torus. The upper maximal
torus need not be supplied as the base change of a lower torus. -/
theorem IsQuasiSplit.root_restrict_ne_zero_of_extension_maximalTorus
    (hG : IsQuasiSplit G) (a : S.toGrp ⟶ G) (ha : IsMaximalSplitTorus a)
    (j : U.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
    (hj : IsMaximalTorus j) (hU : IsSplitTorus U.toGrp)
    (f : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj S ⟶ U)
    (hf : CommGroupScheme.groupHom f ≫ j =
      (GroupScheme.baseChange (algebraBaseMap k L)).map a)
    {β : characterLattice U} (hβ : β ∈ roots j) : f ≫ β ≠ 0 := by
  obtain ⟨T, t, ht, g, hg⟩ :=
    exists_maximalTorus_extension_of_finiteType G a ha.1.1.isTorus ha.1.2
  have hcent₀ : (torusCentralizer a).IsRepresentedBy t :=
    quasiSplitMaximalTorusCentralizer k G hG T S t a g ht ha hg
  have hcent :
      (torusCentralizer (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj S)
        ((GroupScheme.baseChange (algebraBaseMap k L)).map a)).IsRepresentedBy
        ((GroupScheme.baseChange (algebraBaseMap k L)).map t) := by
    rw [torusCentralizer_baseChange]
    exact hcent₀.baseChange (algebraBaseMap k L)
  have htclosed : IsClosedSubgroup
      ((GroupScheme.baseChange (algebraBaseMap k L)).map t) :=
    ht.2.1.baseChange (algebraBaseMap k L)
  have htTorus : IsTorus
      ((GroupScheme.baseChange (algebraBaseMap k L)).obj T.toGrp) :=
    ht.1.baseChange (K := L)
  have hjcent :
      (torusCentralizer (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj S)
        ((GroupScheme.baseChange (algebraBaseMap k L)).map a)).IsRepresentedBy j :=
    hj.isRepresentedBy_torusCentralizer_of_isTorus
      (A := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj S)
      (CommGroupScheme.groupHom f) hf
      ((GroupScheme.baseChange (algebraBaseMap k L)).map t) hcent htclosed htTorus
  exact root_restrict_ne_zero_of_sameField_torusCentralizer (k := L)
    (S := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj S) (T := U)
    (ha.1.1.baseChange (algebraBaseMap k L)) hU
    ((GroupScheme.baseChange (algebraBaseMap k L)).map a) j f hf hjcent hβ

/-- Restrict every actual root of the supplied upper maximal torus to an
actual root of the original maximal split torus. -/
def IsQuasiSplit.rootRestrictionOfExtensionMaximalTorus
    (hG : IsQuasiSplit G) (a : S.toGrp ⟶ G) (ha : IsMaximalSplitTorus a)
    (j : U.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
    (hj : IsMaximalTorus j) (hU : IsSplitTorus U.toGrp)
    (f : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj S ⟶ U)
    (hf : CommGroupScheme.groupHom f ≫ j =
      (GroupScheme.baseChange (algebraBaseMap k L)).map a)
    (β : roots j) : roots a := by
  let α := (characterLattice.baseChangeEquiv (algebraBaseMap k L) S ha.1.1).symm
    (f ≫ β.val)
  refine ⟨α, (mem_roots_baseChange_iff (K := L) G S ha.1.1 a α).mp ?_⟩
  have he : characterLattice.baseChange (algebraBaseMap k L) S α = f ≫ β.val :=
    (characterLattice.baseChangeEquiv (algebraBaseMap k L) S ha.1.1).apply_symm_apply _
  rw [he, ← hf]
  exact (Langlands.GroupScheme.rootRestriction f j ⟨β.val, β.property,
    hG.root_restrict_ne_zero_of_extension_maximalTorus a ha j hj hU f hf β.property⟩).property

/-- The root map is the actual character restriction after base change. -/
@[simp]
theorem IsQuasiSplit.rootRestrictionOfExtensionMaximalTorus_baseChange
    (hG : IsQuasiSplit G) (a : S.toGrp ⟶ G) (ha : IsMaximalSplitTorus a)
    (j : U.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
    (hj : IsMaximalTorus j) (hU : IsSplitTorus U.toGrp)
    (f : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj S ⟶ U)
    (hf : CommGroupScheme.groupHom f ≫ j =
      (GroupScheme.baseChange (algebraBaseMap k L)).map a)
    (β : roots j) :
    characterLattice.baseChange (algebraBaseMap k L) S
        (hG.rootRestrictionOfExtensionMaximalTorus a ha j hj hU f hf β).val =
      f ≫ β.val := by
  change characterLattice.baseChange (algebraBaseMap k L) S
    ((characterLattice.baseChangeEquiv (algebraBaseMap k L) S ha.1.1).symm
      (f ≫ β.val)) = f ≫ β.val
  exact (characterLattice.baseChangeEquiv (algebraBaseMap k L) S ha.1.1).apply_symm_apply _

end Extension
end Langlands.GroupScheme

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

namespace IntegralTorusData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G G' : GroupScheme (Spec (CommRingCat.of K))}
  {D : RelativeComponentModelData R K G}
  {D' : RelativeComponentModelData R K G'}
  {S S' : CommGroupScheme (Spec (CommRingCat.of K))}
  {i : S.toGrp ⟶ G} {i' : S'.toGrp ⟶ G'}
  {A : IntegralTorusData D S i} {B : IntegralTorusData D' S' i'}
  {k : Type u} [Field k] [Algebra k (IsLocalRing.ResidueField R)]
  {H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  {S₀ : CommGroupScheme (Spec (CommRingCat.of k))}

local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k (IsLocalRing.ResidueField R))).obj H).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd H.X.hom
    (algebraBaseMap k (IsLocalRing.ResidueField R)))
  infer_instance

/-- An actual root of the upper residue maximal torus restricts nontrivially
on the prescribed generic source torus, when its residue inclusion is
identified with a maximal split torus of a lower quasi-split group. -/
theorem generic_restriction_ne_zero_of_quasiSplit_residue_root
    (hA : IsSplitTorus A.torus.toGrp) (hB : IsSplitTorus B.torus.toGrp)
    (ρ : A.torus ⟶ B.torus) (χ : characterLattice S')
    (hH : IsQuasiSplit H) (a : S₀.toGrp ⟶ H) (ha : IsMaximalSplitTorus a)
    (eS : (GroupScheme.baseChange
      (algebraBaseMap k (IsLocalRing.ResidueField R))).obj S₀.toGrp ≅ A.specialFibre.toGrp)
    (j : B.specialFibre.toGrp ⟶ (GroupScheme.baseChange
      (algebraBaseMap k (IsLocalRing.ResidueField R))).obj H)
    (hj : IsMaximalTorus j)
    (hρ : eS.hom ≫
      (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map
        (CommGroupScheme.groupHom ρ) ≫ j =
      (GroupScheme.baseChange (algebraBaseMap k (IsLocalRing.ResidueField R))).map a)
    (hχ : B.characterSpecialization hB χ ∈ roots j) :
    A.genericFibreMap B ρ ≫ χ ≠ 0 := by
  let e : (CommGroupScheme.baseChange
      (algebraBaseMap k (IsLocalRing.ResidueField R))).obj S₀ ≅ A.specialFibre :=
    CommGroupScheme.isoOfGroupIso
      (T := (CommGroupScheme.baseChange
        (algebraBaseMap k (IsLocalRing.ResidueField R))).obj S₀)
      (U := A.specialFibre) eS
  let f : (CommGroupScheme.baseChange
      (algebraBaseMap k (IsLocalRing.ResidueField R))).obj S₀ ⟶ B.specialFibre :=
    e.hom ≫
      (CommGroupScheme.baseChange (IntegralModel.residueBaseMap R)).map ρ
  have hf : CommGroupScheme.groupHom f ≫ j =
      (GroupScheme.baseChange (algebraBaseMap k (IsLocalRing.ResidueField R))).map a :=
    hρ
  have hne := hH.root_restrict_ne_zero_of_extension_maximalTorus
    a ha j hj (hB.baseChange _) f hf hχ
  apply (generic_restriction_ne_zero_iff hA hB ρ χ).mpr
  intro hz
  apply hne
  change e.hom ≫
    ((CommGroupScheme.baseChange (IntegralModel.residueBaseMap R)).map ρ ≫
      B.characterSpecialization hB χ) = 0
  rw [hz, Limits.comp_zero]

/-- The residual nonvanishing criterion over a finite lower residue field;
quasi-splitness follows from connected reductivity. -/
theorem generic_restriction_ne_zero_of_finite_residue_root [Finite k]
    (hA : IsSplitTorus A.torus.toGrp) (hB : IsSplitTorus B.torus.toGrp)
    (ρ : A.torus ⟶ B.torus) (χ : characterLattice S')
    (hH : IsConnectedReductive H) (a : S₀.toGrp ⟶ H) (ha : IsMaximalSplitTorus a)
    (eS : (GroupScheme.baseChange
      (algebraBaseMap k (IsLocalRing.ResidueField R))).obj S₀.toGrp ≅ A.specialFibre.toGrp)
    (j : B.specialFibre.toGrp ⟶ (GroupScheme.baseChange
      (algebraBaseMap k (IsLocalRing.ResidueField R))).obj H)
    (hj : IsMaximalTorus j)
    (hρ : eS.hom ≫
      (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map
        (CommGroupScheme.groupHom ρ) ≫ j =
      (GroupScheme.baseChange (algebraBaseMap k (IsLocalRing.ResidueField R))).map a)
    (hχ : B.characterSpecialization hB χ ∈ roots j) :
    A.genericFibreMap B ρ ≫ χ ≠ 0 :=
  generic_restriction_ne_zero_of_quasiSplit_residue_root hA hB ρ χ
    (finiteFieldQuasiSplit k H hH) a ha eS j hj hρ hχ

end IntegralTorusData
end Langlands.BruhatTits.IntegralModels
