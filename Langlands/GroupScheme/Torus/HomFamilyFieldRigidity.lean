import Langlands.GroupScheme.Torus.HomFamilyDiagonalizableReduction
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.GeometricConnectedness

/-! # Base change and rigidity of homomorphism families -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomFamily

section BaseChange

variable {S S' : Scheme.{u}} {G Q N : GroupScheme S}
    (F : ∀ T : Over S, (T ⟶ G.X) → (T ⟶ Q.X) → (T ⟶ N.X))

/-- Pull back a group-parametrized family through the actual point adjunctions. -/
def baseChange (b : S' ⟶ S) (T : Over S')
    (g : T ⟶ ((GroupScheme.baseChange b).obj G).X)
    (q : T ⟶ ((GroupScheme.baseChange b).obj Q).X) :
    T ⟶ ((GroupScheme.baseChange b).obj N).X :=
  (baseChangePointsEquiv b N T).symm
    (F ((Over.map b).obj T) (baseChangePointsEquiv b G T g) (baseChangePointsEquiv b Q T q))

/-- Base change preserves multiplicativity and all-test naturality of a family. -/
theorem isHomFamily_baseChange (hF : IsHomFamily F) (b : S' ⟶ S) :
    IsHomFamily (baseChange F b) where
  map_mul T g q q' := by
    apply (baseChangePointsEquiv b N T).injective
    simp only [baseChange, MulEquiv.apply_symm_apply, map_mul, hF.map_mul]
  naturality {T W} f g q := by
    apply (baseChangePointsEquiv b N W).injective
    simp only [baseChange, MulEquiv.apply_symm_apply, baseChangePointsEquiv_naturality,
      hF.naturality]

/-- A flat surjective change of base detects constancy at the identity parameter on
all scheme tests. -/
theorem eq_one_of_baseChange (hF : IsHomFamily F) (b : S' ⟶ S)
    [Flat b] [Surjective b]
    (ha : ∀ (T : Over S')
      (g : T ⟶ ((GroupScheme.baseChange b).obj G).X)
      (q : T ⟶ ((GroupScheme.baseChange b).obj Q).X),
      baseChange F b T g q = baseChange F b T 1 q)
    {T : Over S} (g : T ⟶ G.X) (q : T ⟶ Q.X) : F T g q = F T 1 q := by
  let T' := (Over.pullback b).obj T
  let p : (Over.map b).obj T' ⟶ T :=
    Over.homMk (pullback.fst T.hom b) (by
      change pullback.fst T.hom b ≫ T.hom = pullback.snd T.hom b ≫ b
      exact pullback.condition)
  have : Epi p.left := by
    change Epi (pullback.fst T.hom b)
    exact Flat.epi_of_flat_of_surjective _
  have : Epi p := Over.epi_of_epi_left p
  apply (cancel_epi p).mp
  let g' := (baseChangePointsEquiv b G T').symm (p ≫ g)
  let q' := (baseChangePointsEquiv b Q T').symm (p ≫ q)
  have he := congrArg (baseChangePointsEquiv b N T') (ha T' g' q')
  simpa only [baseChange, g', q', MulEquiv.apply_symm_apply, map_one,
    ← MonObj.comp_one p, hF.naturality] using he

end BaseChange

/-- The rigidity proposition makes a homomorphism family between diagonalizable groups
constant in its connected algebraic group parameter. -/
theorem eq_one_of_diagonalizableRigidity (hRig : DiagonalizableRigidityStatement.{u})
    {k : Type u} [Field k] {G Q N : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [ConnectedSpace G.X.left]
    (Λ Λ' : Type u) [AddCommGroup Λ] [AddCommGroup Λ']
    [AddGroup.FG Λ] [AddGroup.FG Λ']
    (eQ : Nonempty (Q ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp))
    (eN : Nonempty (N ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ').toGrp))
    {F : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ G.X) → (T ⟶ Q.X) → (T ⟶ N.X)}
    (hF : IsHomFamily F) {T : Over (Spec (CommRingCat.of k))}
    (g : T ⟶ G.X) (q : T ⟶ Q.X) : F T g q = F T 1 q := by
  simpa only [MonObj.comp_one] using
    eq_of_diagonalizableRigidity hRig Λ Λ' inferInstance inferInstance eQ eN
      inferInstance inferInstance inferInstance hF
      (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X) T g q

/-- Constancy over a common diagonalizing field descends to the original field. -/
theorem eq_one_of_commonSplitting (hRig : DiagonalizableRigidityStatement.{u})
    {k : Type u} [Field k] {G Q N : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [ConnectedSpace G.X.left]
    (K : Type u) [Field K] [Algebra k K]
    (Λ Λ' : Type u) [AddCommGroup Λ] [AddCommGroup Λ']
    [AddGroup.FG Λ] [AddGroup.FG Λ']
    (eQ : Nonempty (((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj Q) ≅
        (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp))
    (eN : Nonempty (((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj N) ≅
        (Diagonalizable.groupScheme (CommRingCat.of K) Λ').toGrp))
    {F : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ G.X) → (T ⟶ Q.X) → (T ⟶ N.X)}
    (hF : IsHomFamily F) {T : Over (Spec (CommRingCat.of k))}
    (g : T ⟶ G.X) (q : T ⟶ Q.X) : F T g q = F T 1 q := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hfpqc := fieldExtension_fpqc k K
  let : Surjective b := hfpqc.1
  let : Flat b := hfpqc.2.1
  let : ConnectedSpace ((GroupScheme.baseChange b).obj G).X.left :=
    G.connectedSpace_baseChange_of_connected b
  let : LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom b)
    infer_instance
  let : QuasiCompact ((GroupScheme.baseChange b).obj G).X.hom := by
    change QuasiCompact (pullback.snd G.X.hom b)
    infer_instance
  apply eq_one_of_baseChange F hF b _ g q
  intro V a x
  exact eq_one_of_diagonalizableRigidity hRig Λ Λ' eQ eN
    (isHomFamily_baseChange F hF b) a x

end Langlands.GroupScheme.HomFamily
