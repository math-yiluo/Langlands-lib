import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterWeights
import Langlands.GroupScheme.Dynamic.GeneralLinearProof
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Dynamic.LimitMap
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.Group.GL.UpperTriangularSolvable
import Mathlib.Data.Fin.Tuple.Sort

/-! # Solvability of the points of dynamic unipotent subgroups over a field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n]

section BlockUnipotent

variable (A : Type u) [CommRing A] (e : n → ℤ)

/-- An enumeration `Fin N ≃ n` along which the weights `e` are antitone. -/
def antitoneEnumeration : Fin (Fintype.card n) ≃ n :=
  (Tuple.sort fun i => -e ((Fintype.equivFin n).symm i)).trans (Fintype.equivFin n).symm

omit [DecidableEq n] in
theorem antitone_antitoneEnumeration : Antitone (e ∘ antitoneEnumeration e) := by
  intro i j hij
  have h := Tuple.monotone_sort (fun i => -e ((Fintype.equivFin n).symm i)) hij
  simp only [Function.comp_apply, neg_le_neg_iff] at h
  exact h

/-- Reindexing a block unipotent matrix along `antitoneEnumeration e` makes it upper
triangular. -/
def blockUnipotentToUpper :
    blockUnipotentSubgroup A e →* Langlands.GeneralLinear.upperTriangularSubgroup
      (Fintype.card n) A where
  toFun g := ⟨Units.map (Matrix.reindexAlgEquiv A A (antitoneEnumeration e).symm).toMonoidHom
      (g : GL n A), by
    intro i j hij
    change ((g : GL n A) : Matrix n n A) (antitoneEnumeration e i) (antitoneEnumeration e j) = 0
    have hle : e (antitoneEnumeration e i) ≤ e (antitoneEnumeration e j) :=
      antitone_antitoneEnumeration e (le_of_lt hij)
    rw [g.property _ _ hle]
    exact Matrix.one_apply_ne fun h => hij.ne ((antitoneEnumeration e).injective h).symm⟩
  map_one' := by
    ext
    simp
  map_mul' g h := by
    ext
    simp

theorem blockUnipotentToUpper_injective :
    Function.Injective (blockUnipotentToUpper A e) := by
  intro g h hgh
  apply Subtype.ext
  apply Units.ext
  have := congrArg (fun x : Langlands.GeneralLinear.upperTriangularSubgroup (Fintype.card n) A =>
    ((x : Langlands.GeneralLinear (Fintype.card n) A) : Matrix (Fin (Fintype.card n))
      (Fin (Fintype.card n)) A)) hgh
  exact (Matrix.reindexAlgEquiv A A (antitoneEnumeration e).symm).injective this

/-- Block unipotent invertible matrices over any commutative ring form a solvable group. -/
theorem isSolvable_blockUnipotentSubgroup :
    Group.IsSolvable (blockUnipotentSubgroup A e) := by
  have := Langlands.GeneralLinear.UpperTriangularSolvable.isSolvable (Fintype.card n) A
  exact Group.isSolvable_of_isSolvable_injective (blockUnipotentToUpper_injective A e)

end BlockUnipotent

section Unipotent

variable {K : Type u} [Field K]

/-- Over a field, for every cocharacter `ψ` of `GL_n` and every test scheme `U`, the group of
points of `U(ψ)` over `U` is solvable. -/
theorem isSolvable_unipotent_carrier
    (ψ : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ groupScheme n (CommRingCat.of K))
    (U : Over (Spec (CommRingCat.of K))) :
    Group.IsSolvable ((Dynamic.unipotent ψ).carrier U) := by
  obtain ⟨g, e, hge⟩ := exists_matrix_innerIso_comp_eq_diagonalCocharacter ψ
  set c := constantPoint (groupScheme n (CommRingCat.of K)) (baseOfMatrix _ g) U
  have hmem : ∀ x : (Dynamic.unipotent ψ).carrier U,
      pointsEquiv n _ U (MulAut.conj c (x : U ⟶ (groupScheme n (CommRingCat.of K)).X)) ∈
        blockUnipotentSubgroup Γ(U.left, ⊤) e := by
    intro x
    have h := (Dynamic.mem_unipotent_conj ψ (baseOfMatrix _ g)).mp x.2
    rw [hge, (dynamicStatement.1 n _ e).2.2] at h
    exact h
  let f : (Dynamic.unipotent ψ).carrier U →* blockUnipotentSubgroup Γ(U.left, ⊤) e :=
    ((pointsEquiv n _ U).toMonoidHom.comp
      ((MulAut.conj c).toMonoidHom.comp (Subgroup.subtype _))).codRestrict _ hmem
  have hf : Function.Injective f := by
    intro x y hxy
    have h := congrArg (fun z : blockUnipotentSubgroup Γ(U.left, ⊤) e =>
      (z : GL n Γ(U.left, ⊤))) hxy
    exact Subtype.ext ((MulAut.conj c).injective ((pointsEquiv n _ U).injective h))
  have := isSolvable_blockUnipotentSubgroup Γ(U.left, ⊤) e
  exact Group.isSolvable_of_isSolvable_injective hf

end Unipotent

end Langlands.GroupScheme.GeneralLinear

namespace Langlands.GroupScheme.Dynamic

variable {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))}

/-- Over a field, for every affine group scheme `G` locally of finite type, every cocharacter
`χ` of `G` and every test scheme `U`, the group of points of `U(χ)` over `U` is solvable. -/
theorem isSolvable_unipotent_carrier [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ G) (U : Over (Spec (CommRingCat.of K))) :
    Group.IsSolvable ((unipotent χ).carrier U) := by
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement K G inferInstance inferInstance
  have hmono : Mono ρ.hom.hom.left := by
    have : IsClosedImmersion ρ.hom.hom.left := hρ
    infer_instance
  let f : (unipotent χ).carrier U →* (unipotent (χ ≫ ρ)).carrier U :=
    { toFun := fun x => ⟨(x : U ⟶ G.X) ≫ ρ.hom.hom, unipotent_le_comap χ ρ U x.2⟩
      map_one' := by
        apply Subtype.ext
        exact MonObj.one_comp _
      map_mul' := fun x y => by
        apply Subtype.ext
        exact MonObj.mul_comp _ _ _ }
  have hf : Function.Injective f := by
    intro x y hxy
    have h := congrArg (fun z : (unipotent (χ ≫ ρ)).carrier U =>
      (z : U ⟶ (GeneralLinear.groupScheme (Fin N) (CommRingCat.of K)).X)) hxy
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact (cancel_mono ρ.hom.hom.left).1 (congrArg CommaMorphism.left h)
  have := GeneralLinear.isSolvable_unipotent_carrier (χ ≫ ρ) U
  exact Group.isSolvable_of_isSolvable_injective hf

/-- For a separated group scheme, the points of `P(χ)` over `U` form a solvable group as soon as
those of `Z(χ)` do and those of `U(χ)` do: `U(χ)(U)` is the kernel of the surjective limit
homomorphism `P(χ)(U) → Z(χ)(U)`. -/
theorem isSolvable_parabolic_carrier {S : Scheme.{u}} {G : GroupScheme S} [IsSeparated G.X.hom]
    (χ : (Gm S).toGrp ⟶ G) (U : Over S) [Group.IsSolvable ((unipotent χ).carrier U)]
    [Group.IsSolvable ((centralizer χ).carrier U)] :
    Group.IsSolvable ((parabolic χ).carrier U) := by
  refine Group.isSolvable_of_ker_le_range
    (Subgroup.inclusion (unipotent_le_parabolic χ U)) (limitHom χ U) ?_
  intro g hg
  rw [ker_limitHom, Subgroup.mem_subgroupOf] at hg
  exact ⟨⟨g, hg⟩, rfl⟩

end Langlands.GroupScheme.Dynamic
