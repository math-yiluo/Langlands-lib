import Langlands.GroupScheme.Torus.FibrewiseMaximalTransport
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Torus.FieldPointMaximality

/-! # Étale descent of relative tori and transport of fibrewise maximality -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace RelativeTorus

variable {S U : Scheme.{u}} {G : GroupScheme S}

/-- Compose a chosen splitting cover upstairs with the étale surjection. -/
def IsTorus.descendedSplittingCover (p : U ⟶ S) [Etale p] [Surjective p]
    (h : IsTorus ((GroupScheme.baseChange p).obj G)) :
    Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
  let 𝒰 := Classical.choose h
  Scheme.Cover.mkOfCovers 𝒰.I₀ 𝒰.X (fun j => 𝒰.f j ≫ p)
      (fun s => by
        obtain ⟨x, rfl⟩ := p.surjective s
        obtain ⟨j, y, hy⟩ := 𝒰.exists_eq x
        exact ⟨j, y, by simp only [Scheme.Hom.comp_apply, hy]⟩)
      (fun j => by
        let : Etale (𝒰.f j) := 𝒰.map_prop j
        infer_instance)

/-- The descended cover splits the original group on each member. -/
theorem IsTorus.descendedSplittingCover_splits (p : U ⟶ S)
    [Etale p] [Surjective p] (h : IsTorus ((GroupScheme.baseChange p).obj G))
    (j : (h.descendedSplittingCover p).I₀) :
    IsSplitTorus ((GroupScheme.baseChange ((h.descendedSplittingCover p).f j)).obj G) := by
  exact IsSplitTorus.of_iso
    (baseChangeCompIso p ((Classical.choose h).f j) G) (Classical.choose_spec h j)

/-- An étale surjective pullback detects the relative-torus property. -/
theorem IsTorus.of_baseChange_of_etale (p : U ⟶ S) [Etale p] [Surjective p]
    (h : IsTorus ((GroupScheme.baseChange p).obj G)) : IsTorus G :=
  ⟨h.descendedSplittingCover p, h.descendedSplittingCover_splits p⟩

/-- The relative-torus property can be checked on any étale surjective pullback. -/
theorem isTorus_baseChange_iff_of_etale (p : U ⟶ S) [Etale p] [Surjective p] :
    IsTorus ((GroupScheme.baseChange p).obj G) ↔ IsTorus G :=
  ⟨IsTorus.of_baseChange_of_etale p, IsTorus.baseChange p⟩

end RelativeTorus

variable {S U : Scheme.{u}} {T : CommGroupScheme S} {G H : GroupScheme S}

variable [Smooth G.X.hom] [IsAffineHom G.X.hom]

omit [Smooth G.X.hom] [IsAffineHom G.X.hom] in
/-- A closed torus is fibrewise maximal if its pullback along a surjection is so. -/
theorem IsFibrewiseMaximalTorus.of_baseChange {i : T.toGrp ⟶ G}
    (p : U ⟶ S) [Surjective p] (hi : IsClosedSubgroup i)
    (h : IsFibrewiseMaximalTorus
      (T := (CommGroupScheme.baseChange p).obj T) ((GroupScheme.baseChange p).map i)) :
    IsFibrewiseMaximalTorus i := by
  intro s
  obtain ⟨x, rfl⟩ := p.surjective s
  let a := S.fromSpecResidueField (p x)
  let c := Spec.map (p.residueFieldMap x)
  let : Algebra (S.residueField (p x) : Type u) (U.residueField x : Type u) :=
    (p.residueFieldMap x).hom.toAlgebra
  apply IsMaximalTorus.of_baseChange
    (k := (S.residueField (p x) : Type u))
    (T := (CommGroupScheme.baseChange a).obj T)
    (K := (U.residueField x : Type u)) (hi.baseChange a)
  change IsMaximalTorus
    (T := (CommGroupScheme.baseChange c).obj ((CommGroupScheme.baseChange a).obj T))
    ((GroupScheme.baseChange c).map ((GroupScheme.baseChange a).map i))
  apply isMaximalTorus_baseChange_comp a c T i
  rw [show c ≫ a = U.fromSpecResidueField x ≫ p from
    p.SpecMap_residueFieldMap_fromSpecResidueField x]
  exact isMaximalTorus_of_baseChange_comp p (U.fromSpecResidueField x) T i (h x)

end Langlands.GroupScheme
