import Langlands.GroupScheme.Dynamic.BaseChange
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.CocharacterTransport

/-! # Dynamic subgroup functors and the canonical descent transport -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)
  (G : GroupScheme B)

namespace SubgroupFunctor

/-- Transport a subgroup functor through pullback and the canonical descent identification. -/
def descentTransport (F : SubgroupFunctor ((GroupScheme.baseChange b).obj G)) :
    SubgroupFunctor ((GroupScheme.baseChange b).obj G) :=
  (F.baseChange a).comap (descentBaseChangeIso b a ha G).inv

/-- Membership in a transported subgroup is membership after the inverse descent map and pullback. -/
theorem mem_descentTransport (F : SubgroupFunctor ((GroupScheme.baseChange b).obj G))
    {T : Over S} {x : T ⟶ ((GroupScheme.baseChange b).obj G).X} :
    x ∈ (descentTransport b a ha G F).carrier T ↔
      baseChangePointsEquiv a ((GroupScheme.baseChange b).obj G) T
        (x ≫ (descentBaseChangeIso b a ha G).inv.hom.hom) ∈
          F.carrier ((Over.map a).obj T) :=
  Iff.rfl

/-- A subgroup functor pulled back from `B` is preserved by its canonical descent identification. -/
theorem baseChange_descent_comap (F : SubgroupFunctor G) :
    ((F.baseChange b).baseChange a).comap (descentBaseChangeIso b a ha G).inv =
      F.baseChange b := by
  ext T x
  rw [mem_comap, mem_baseChange, mem_baseChange, mem_baseChange]
  have hx := baseChangePointsEquiv_descent b a ha G T
    (x ≫ (descentBaseChangeIso b a ha G).inv.hom.hom)
  simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id] at hx
  rw [hx]
  constructor
  · exact F.comp_mem (descentTestIso b a ha T).hom
  · intro h
    have h' := F.comp_mem (descentTestIso b a ha T).inv h
    simpa only [Iso.inv_hom_id_assoc] using h'

/-- Every subgroup functor obtained by base change is fixed by the canonical descent transport. -/
theorem descentTransport_baseChange (F : SubgroupFunctor G) :
    descentTransport b a ha G (F.baseChange b) = F.baseChange b :=
  baseChange_descent_comap b a ha G F

end SubgroupFunctor

namespace Dynamic

variable (χ : (Gm S).toGrp ⟶ (GroupScheme.baseChange b).obj G)

/-- Canonical cocharacter transport carries its parabolic by pullback and the descent isomorphism. -/
theorem parabolic_transportCocharacter :
    parabolic (transportCocharacter b a ha G χ) =
      ((parabolic χ).baseChange a).comap (descentBaseChangeIso b a ha G).inv := by
  have hc : transportCocharacter b a ha G χ ≫ (descentBaseChangeIso b a ha G).inv =
      baseChangeCocharacter a χ := by
    simp only [transportCocharacter, baseChangeCocharacter, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [parabolic_eq_comap_of_iso _ (descentBaseChangeIso b a ha G).symm,
    Iso.symm_hom, hc, parabolic_baseChange]

/-- Dynamic parabolics commute with the subgroup-functor descent transport. -/
theorem parabolic_transportCocharacter_eq_descentTransport :
    parabolic (transportCocharacter b a ha G χ) =
      SubgroupFunctor.descentTransport b a ha G (parabolic χ) :=
  parabolic_transportCocharacter b a ha G χ

/-- If a dynamic parabolic descends as a subgroup functor, every canonical transport defines it. -/
theorem parabolic_transportCocharacter_eq_baseChange (F : SubgroupFunctor G)
    (hχ : parabolic χ = F.baseChange b) :
    parabolic (transportCocharacter b a ha G χ) = F.baseChange b := by
  rw [parabolic_transportCocharacter, hχ, SubgroupFunctor.baseChange_descent_comap]

end Dynamic

end Langlands.GroupScheme
