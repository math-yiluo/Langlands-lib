import Langlands.Cohomology.EquivariantComposite.Cofree
import Langlands.Cohomology.SmoothExt
import Langlands.Cohomology.DivisibleSystem.PermutationProjective

/-! # Higher invariants of smooth cofree representations -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.EquivariantComposite

universe u

variable (R G : Type u) [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The invariants functor on smooth representations. -/
abbrev invariants : SmoothRep.{u,u,u} R G ⥤ ModuleCat.{u} R :=
  Langlands.Cohomology.smoothInvariantsFunctor R G

/-- An invariant function is constant, and evaluation at one gives its value. -/
def cofreeInvariantsEquiv (M : ModuleCat.{u} R) :
    (cofreeObj R G M).representation.invariants ≃ₗ[R] M where
  toFun s := s.val.val 1
  invFun m := ⟨⟨fun _ => m, ⟨⊤, fun _ => rfl⟩⟩, fun _ => rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    have h := congrFun (congrArg Subtype.val (s.property g⁻¹)) 1
    change s.val.val ((g⁻¹)⁻¹ * 1) = s.val.val 1 at h
    simpa using h.symm
  right_inv _ := rfl

/-- Cofree representations have the original coefficient module as invariants. -/
def cofreeInvariantsIso : cofree R G ⋙ invariants R G ≅ 𝟭 (ModuleCat.{u} R) :=
  NatIso.ofComponents (fun M => (cofreeInvariantsEquiv R G M).toModuleIso)
    (fun _ => rfl)

/-- Higher derived functors of the identity vanish. -/
theorem isZero_identity_rightDerived (M : ModuleCat.{u} R) (q : ℕ) :
    IsZero (((𝟭 (ModuleCat.{u} R)).rightDerived (q + 1)).obj M) := by
  let I := injectiveResolution M
  refine IsZero.of_iso ?_ (I.isoRightDerivedObj (𝟭 _) (q + 1))
  have h := I.cocomplex_exactAt_succ q
  have e := ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R)
    (ComplexShape.up ℕ) (q + 1)).mapIso
      ((Functor.mapHomologicalComplexIdIso (ModuleCat.{u} R)
        (ComplexShape.up ℕ)).app I.cocomplex))
  exact IsZero.of_iso ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 h) e

/-- Smooth cofree representations are acyclic for invariants over every coefficient ring. -/
theorem isZero_cofree_higherInvariants (M : ModuleCat.{u} R) (q : ℕ) :
    IsZero (((invariants R G).rightDerived (q + 1)).obj ((cofree R G).obj M)) := by
  let e := DerivedComparison.rightDerivedCompIso (𝟭 (ModuleCat.{u} R))
    (𝟭 (ModuleCat.{u} R)) (cofree R G) (invariants R G)
    (Functor.leftUnitor _ ≪≫ (cofreeInvariantsIso R G).symm) (q + 1)
  exact IsZero.of_iso (isZero_identity_rightDerived R M q) (e.app M).symm

/-- Hom from the trivial smooth representation is the module of invariant vectors. -/
def trivialHomEquiv (V : SmoothRep.{u,u,u} R G) :
    (trivialSmoothRep R G ⟶ V) ≃ₗ[R] V.representation.invariants where
  toFun f := ⟨SmoothRep.hom f (1 : R), fun g => by
    have h := Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom f) g (1 : R)
    exact h.symm⟩
  invFun v := SmoothRep.ofHom
    { toLinearMap := LinearMap.toSpanSingleton R V v.val
      isIntertwining' g := by
        apply LinearMap.ext
        intro r
        change R at r
        change r • v.val = V.representation g (r • v.val)
        simp [v.property g] }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro r
    change R at r
    let f' : R →ₗ[R] V := (SmoothRep.hom f).toLinearMap
    change r • f' (1 : R) = f' r
    simpa using (map_smul f' r (1 : R)).symm
  right_inv v := by apply Subtype.ext; exact one_smul R v.val

/-- The preceding identification is natural in the representation. -/
def trivialHomIso : SmoothHomComplex.homFunctor R G (trivialSmoothRep R G) ≅ invariants R G :=
  NatIso.ofComponents (fun V => (trivialHomEquiv R G V).toModuleIso)
    (fun _ => rfl)

end Langlands.Cohomology.EquivariantComposite
