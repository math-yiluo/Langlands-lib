import Langlands.GroupScheme.Rational.QuasiSplitCentralizerTorus
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Torus.MaximalSelfCentralizing
import Langlands.GroupScheme.Torus.LatticeBaseInvariants
import Langlands.GroupScheme.Absolute.RegularCocharacterWeights
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Absolute.SplitTorusDynamicDescent

/-! # Regular descended cocharacters of torus centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace Langlands.GroupScheme

section Regularity

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- A cocharacter whose whole centralizer is represented by its containing split
torus has nonzero pairing with every actual root. -/
theorem isRegularCocharacter_of_centralizer_isRepresentedBy_torus
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (hi : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy i) :
    IsRegularCocharacter i ν := by
  intro α hα hzero
  obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα.2
  have hfixed : X.toMul.val ∈
      (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).carrier _ := by
    apply (dynamicLie k G _ X.toMul).1.mpr
    have h := weightSpace_le_weightSpace_cocharacter ν i α hX
    rwa [hzero] at h
  rw [← hi.2] at hfixed
  have hXzero : X ∈ weightSpace i 0 :=
    Lie.mem_weightSpace_zero_of_mem_torusCentralizer i X.toMul
      (range_le_torusCentralizer i _ hfixed)
  exact hX0 ((Submodule.disjoint_def.mp (weightSpace_disjoint hT i hα.1)) X hX hXzero)

end Regularity

namespace TorusCentralizerTorusData

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ G} (C : TorusCentralizerTorusData a)

/-- A torus representing the whole centralizer of a commutative subgroup is
self-centralizing on every scheme test. -/
theorem selfCentralizing :
    torusCentralizer C.inclusion = SubgroupFunctor.range C.inclusion := by
  apply le_antisymm
  · intro U x hx
    rw [C.represents.2]
    intro V q t
    have h := hx V q (t ≫ (torusCentralizerFactor a C.represents).hom.hom)
    simpa only [Category.assoc, ← Grp.comp_hom_hom, torusCentralizerFactor_comp] using h
  · exact range_le_torusCentralizer C.inclusion

/-- The supplied centralizer torus is an actual maximal torus of the ambient
group. No reductivity or maximality of the original subgroup is needed. -/
theorem isMaximalTorus : IsMaximalTorus C.inclusion :=
  isMaximalTorus_of_torusCentralizer_eq C.isTorus C.isClosedSubgroup C.selfCentralizing

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Compose an original-field separating cocharacter with the canonical factor
of the split torus through its actual centralizer torus. -/
def regularCocharacter (hA : IsSplitTorus A.toGrp) : cocharacterLattice C.torus :=
  centralizingCocharacter hA a ≫
    Additive.ofMul (torusCentralizerFactor a C.represents)

/-- The constructed original-field cocharacter has exactly the supplied torus
as its whole dynamic centralizer. -/
theorem regularCocharacter_centralizer (hA : IsSplitTorus A.toGrp) :
    Dynamic.centralizer
        (CommGroupScheme.groupHom (C.regularCocharacter hA) ≫ C.inclusion) =
      SubgroupFunctor.range C.inclusion := by
  change Dynamic.centralizer
    ((CommGroupScheme.groupHom (centralizingCocharacter hA a) ≫
      torusCentralizerFactor a C.represents) ≫ C.inclusion) = _
  rw [Category.assoc, torusCentralizerFactor_comp, centralizingCocharacter_spec]
  exact C.represents.2.symm

variable (K : Type u) [Field K] [Algebra k K]

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) C.torus
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) C.inclusion

local instance : IsAffineHom (G_K).X.hom :=
  MorphismProperty.baseChange_obj (P := @IsAffineHom) b G.X inferInstance

local instance : LocallyOfFiniteType (G_K).X.hom :=
  MorphismProperty.baseChange_obj (P := @LocallyOfFiniteType) b G.X inferInstance

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- Self-centralization makes this same torus maximal after every field
extension, without a maximal-torus ascent premise. -/
theorem isMaximalTorus_baseChange :
    IsMaximalTorus (T := T_K) i_K :=
  isMaximalTorus_baseChange_of_torusCentralizer_eq K
    C.isTorus C.isClosedSubgroup C.selfCentralizing

/-- The canonical base change of the original-field cocharacter still has the
same base-changed torus as its whole centralizer. -/
theorem regularCocharacter_baseChange_centralizer (hA : IsSplitTorus A.toGrp) :
    Dynamic.centralizer
        (CommGroupScheme.groupHom
          (cocharacterLattice.baseChange b C.torus (C.regularCocharacter hA)) ≫ i_K) =
      SubgroupFunctor.range i_K := by
  rw [cocharacterLattice.groupHom_baseChange_dynamic,
    ← Dynamic.baseChangeCocharacter_comp, Dynamic.centralizer_baseChange,
    C.regularCocharacter_centralizer hA]
  exact (SubgroupFunctor.range_baseChangeHom b C.inclusion).symm

/-- Over every splitting field of the actual centralizer torus, the canonical
base change of the constructed ground-field cocharacter is regular. -/
theorem regularCocharacter_baseChange_isRegular
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus (T_K).toGrp) :
    IsRegularCocharacter (T := T_K) i_K
      (cocharacterLattice.baseChange b C.torus (C.regularCocharacter hA)) := by
  apply isRegularCocharacter_of_centralizer_isRepresentedBy_torus hT i_K
  have : Mono (i_K).hom.hom := (C.represents.baseChange b).1
  exact ⟨inferInstance, (C.regularCocharacter_baseChange_centralizer K hA).symm⟩

/-- Ordinary Galois fixedness comes from the constructed ground-field
cocharacter, without any descent assumption on invariant lattices. -/
theorem regularCocharacter_baseChange_galois
    (hA : IsSplitTorus A.toGrp) (σ : K ≃ₐ[k] K) :
    cocharacterLattice.galoisRepresentation k K C.torus σ
        (cocharacterLattice.baseChange b C.torus (C.regularCocharacter hA)) =
      cocharacterLattice.baseChange b C.torus (C.regularCocharacter hA) :=
  cocharacterLattice.galoisRepresentation_baseChange k K C.torus σ
    (C.regularCocharacter hA)

end TorusCentralizerTorusData

end Langlands.GroupScheme
