import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerRootModel
import Langlands.GroupScheme.Absolute.SplitTorusDynamicDescent
import Langlands.GroupScheme.Torus.LatticeBaseInvariants
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction

/-! # Rational compatible tori and their separating cocharacters -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

set_option autoImplicit false

section Model

variable {G M : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A rational maximal torus containing the given torus and factoring through its
represented centralizer, with maximality in both groups over the original field. -/
structure TorusCentralizerRationalModel (a : A.toGrp ⟶ G) (j : M ⟶ G) where
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  ambient : torus.toGrp ⟶ G
  centralizer : torus.toGrp ⟶ M
  factor : A ⟶ torus
  ambient_maximal : IsMaximalTorus ambient
  centralizer_maximal : IsMaximalTorus centralizer
  factor_closed : IsClosedSubgroup (CommGroupScheme.groupHom factor)
  centralizer_comp : centralizer ≫ j = ambient
  factor_comp : CommGroupScheme.groupHom factor ≫ ambient = a

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Choose compatible rational maximal tori for an actual split-torus centralizer
over an arbitrary field. Splitness of the chosen maximal torus is not required. -/
def torusCentralizerRationalModel
    (a : A.toGrp ⟶ G) (ha : IsSplitSubtorus a) (j : M ⟶ G)
    (hj : (torusCentralizer a).IsRepresentedBy j) :
    TorusCentralizerRationalModel a j := Classical.choice <| by
  obtain ⟨T, i, hi, f, hf⟩ :=
    exists_maximalTorus_extension_of_finiteType G a ha.1.isTorus ha.2
  have hjc : IsClosedSubgroup j := ha.1.isClosedSubgroup_torusCentralizer a hj
  let iM : T.toGrp ⟶ M :=
    hj.factorHom i (range_le_torusCentralizer_of_factor a i f hf)
  have hiM : iM ≫ j = i := hj.factorHom_comp _ _
  exact
    ⟨{ torus := T
       ambient := i
       centralizer := iM
       factor := Additive.ofMul f
       ambient_maximal := hi
       centralizer_maximal := IsMaximalTorus.of_comp hjc (hiM.symm ▸ hi)
       factor_closed := IsClosedSubgroup.of_comp hi.2.1 (hf.symm ▸ ha.2)
       centralizer_comp := hiM
       factor_comp := hf }⟩

end Model

namespace TorusCentralizerRationalModel

variable {G M : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {a : A.toGrp ⟶ G} {j : M ⟶ G}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (C : TorusCentralizerRationalModel a j)

/-- The original-field separating cocharacter, composed into the rational torus. -/
def cocharacter (hA : IsSplitTorus A.toGrp) : cocharacterLattice C.torus :=
  centralizingCocharacter hA a ≫ C.factor

/-- The same original-field cocharacter presents the supplied torus centralizer. -/
theorem cocharacter_centralizer (hA : IsSplitTorus A.toGrp) :
    Dynamic.centralizer (CommGroupScheme.groupHom (C.cocharacter hA) ≫ C.ambient) =
      torusCentralizer a := by
  change Dynamic.centralizer
    ((CommGroupScheme.groupHom (centralizingCocharacter hA a) ≫
      CommGroupScheme.groupHom C.factor) ≫ C.ambient) = _
  rw [Category.assoc, C.factor_comp, centralizingCocharacter_spec]

section BaseChange

variable {S' : Scheme.{u}} (b : S' ⟶ Spec (CommRingCat.of k))

/-- The base change of the original-field cocharacter presents the base-changed
torus centralizer on all test schemes. -/
theorem cocharacter_centralizer_baseChange (hA : IsSplitTorus A.toGrp) :
    Dynamic.centralizer
        (CommGroupScheme.groupHom (cocharacterLattice.baseChange b C.torus
          (C.cocharacter hA)) ≫ (GroupScheme.baseChange b).map C.ambient) =
      (torusCentralizer a).baseChange b := by
  rw [cocharacterLattice.groupHom_baseChange_dynamic,
    ← Dynamic.baseChangeCocharacter_comp, Dynamic.centralizer_baseChange,
    C.cocharacter_centralizer hA]

/-- The base change of the supplied inclusion represents the centralizer of the
base change of the original-field separating cocharacter. -/
theorem cocharacter_baseChange_isRepresentedBy
    (hA : IsSplitTorus A.toGrp) (hj : (torusCentralizer a).IsRepresentedBy j) :
    (Dynamic.centralizer
      (CommGroupScheme.groupHom (cocharacterLattice.baseChange b C.torus
        (C.cocharacter hA)) ≫ (GroupScheme.baseChange b).map C.ambient)).IsRepresentedBy
      ((GroupScheme.baseChange b).map j) := by
  rw [C.cocharacter_centralizer_baseChange b hA]
  exact hj.baseChange b

/-- The separating cocharacter also presents the centralizer of the actual
base-changed subtorus. -/
theorem cocharacter_centralizer_eq_baseChangedTorusCentralizer
    (hA : IsSplitTorus A.toGrp) :
    Dynamic.centralizer
        (CommGroupScheme.groupHom (cocharacterLattice.baseChange b C.torus
          (C.cocharacter hA)) ≫ (GroupScheme.baseChange b).map C.ambient) =
      torusCentralizer (T := (CommGroupScheme.baseChange b).obj A)
        ((GroupScheme.baseChange b).map a) := by
  rw [C.cocharacter_centralizer_baseChange b hA, torusCentralizer_baseChange]

end BaseChange

section Galois

variable (E : Type u) [Field E] [Algebra k E]

/-- The chosen cocharacter remains fixed by the ordinary cocharacter Galois
action, since it is the base change of an actual original-field cocharacter. -/
theorem cocharacter_baseChange_galois (hA : IsSplitTorus A.toGrp) (σ : E ≃ₐ[k] E) :
    cocharacterLattice.galoisRepresentation k E C.torus σ
        (cocharacterLattice.baseChange (algebraBaseMap k E) C.torus (C.cocharacter hA)) =
      cocharacterLattice.baseChange (algebraBaseMap k E) C.torus (C.cocharacter hA) :=
  cocharacterLattice.galoisRepresentation_baseChange k E C.torus σ (C.cocharacter hA)

end Galois

section Roots

variable [IsAffineHom M.X.hom] [LocallyOfFiniteType M.X.hom]

/-- The actual roots of the original-field centralizer are the zero-pairing
ambient roots for this same rational torus and separating cocharacter. -/
theorem relativeRoots_eq_pairing
    (hA : IsSplitTorus A.toGrp) (hj : (torusCentralizer a).IsRepresentedBy j) :
    relativeRoots C.centralizer =
      {α | α ∈ relativeRoots C.ambient ∧
        latticePairing C.torus α (C.cocharacter hA) = 0} := by
  apply relativeRoots_centralizer_factor dynamicLie C.ambient C.centralizer j
    C.centralizer_comp (C.cocharacter hA)
  rw [C.cocharacter_centralizer hA]
  exact hj

variable {E : Type u} [Field E] (b : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of k))

/-- After any field base map, actual centralizer roots remain precisely the
ambient roots with zero pairing against the base-changed original cocharacter. -/
theorem relativeRoots_baseChange_eq_pairing
    (hA : IsSplitTorus A.toGrp) (hj : (torusCentralizer a).IsRepresentedBy j) :
    haveI : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
      MorphismProperty.baseChange_obj (P := @IsAffineHom) b G.X inferInstance
    haveI : IsAffineHom ((GroupScheme.baseChange b).obj M).X.hom :=
      MorphismProperty.baseChange_obj (P := @IsAffineHom) b M.X inferInstance
    relativeRoots ((GroupScheme.baseChange b).map C.centralizer) =
      {α | α ∈ relativeRoots ((GroupScheme.baseChange b).map C.ambient) ∧
        latticePairing ((CommGroupScheme.baseChange b).obj C.torus) α
          (cocharacterLattice.baseChange b C.torus (C.cocharacter hA)) = 0} := by
  let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
    MorphismProperty.baseChange_obj (P := @IsAffineHom) b G.X inferInstance
  let : IsAffineHom ((GroupScheme.baseChange b).obj M).X.hom :=
    MorphismProperty.baseChange_obj (P := @IsAffineHom) b M.X inferInstance
  let : LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom :=
    MorphismProperty.baseChange_obj (P := @LocallyOfFiniteType) b G.X inferInstance
  let : LocallyOfFiniteType ((GroupScheme.baseChange b).obj M).X.hom :=
    MorphismProperty.baseChange_obj (P := @LocallyOfFiniteType) b M.X inferInstance
  apply relativeRoots_centralizer_factor dynamicLie
    ((GroupScheme.baseChange b).map C.ambient)
    ((GroupScheme.baseChange b).map C.centralizer) ((GroupScheme.baseChange b).map j)
    (by rw [← Functor.map_comp, C.centralizer_comp])
    (cocharacterLattice.baseChange b C.torus (C.cocharacter hA))
  exact C.cocharacter_baseChange_isRepresentedBy b hA hj

end Roots

end TorusCentralizerRationalModel

end Langlands.GroupScheme
