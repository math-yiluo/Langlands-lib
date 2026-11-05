import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Rational.RationalMaximalTorusDensityReduction
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # An actual maximal-torus parameter scheme and its quotient map -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The geometric, all-test fiber and conjugation compatibility properties required
of one actual maximal-torus parameter scheme `Q` and one actual map `q : G.X ⟶ Q`.
This predicate does not assert the existence of such a scheme or map. -/
def IsMaximalTorusParameter
    {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T₀ : CommGroupScheme (Spec (CommRingCat.of k))} (j₀ : T₀.toGrp ⟶ G)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q) : Prop :=
  (Smooth Q.hom ∧ IsSeparated Q.hom ∧ LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom) ∧
    (Smooth q.left ∧ Surjective q.left ∧ QuasiCompact q.left) ∧
      (∀ (U : Over (Spec (CommRingCat.of k))) (g h : U ⟶ G.X),
        g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (torusNormalizer j₀).carrier U) ∧
      TorusParameterConjugationCompatible j₀ q

namespace IsMaximalTorusParameter

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T₀ : CommGroupScheme (Spec (CommRingCat.of k))} {j₀ : T₀.toGrp ⟶ G}
  {Q : Over (Spec (CommRingCat.of k))} {q : G.X ⟶ Q}

/-- The parameter scheme is smooth over the ground field. -/
theorem smooth (h : IsMaximalTorusParameter j₀ q) : Smooth Q.hom :=
  h.1.1

/-- The parameter scheme is separated over the ground field. -/
theorem isSeparated (h : IsMaximalTorusParameter j₀ q) : IsSeparated Q.hom :=
  h.1.2.1

/-- The parameter scheme is locally of finite type over the ground field. -/
theorem locallyOfFiniteType (h : IsMaximalTorusParameter j₀ q) :
    LocallyOfFiniteType Q.hom :=
  h.1.2.2.1

/-- The parameter scheme is quasi-compact over the ground field. -/
theorem quasiCompact (h : IsMaximalTorusParameter j₀ q) : QuasiCompact Q.hom :=
  h.1.2.2.2

/-- The parameter map is smooth. -/
theorem smooth_map (h : IsMaximalTorusParameter j₀ q) : Smooth q.left :=
  h.2.1.1

/-- The parameter map is surjective on the underlying scheme spaces. -/
theorem surjective_map (h : IsMaximalTorusParameter j₀ q) : Surjective q.left :=
  h.2.1.2.1

/-- The parameter map is quasi-compact. -/
theorem quasiCompact_map (h : IsMaximalTorusParameter j₀ q) : QuasiCompact q.left :=
  h.2.1.2.2

/-- On every scheme test, equal parameter images are exactly right-normalizer cosets. -/
theorem fiber_iff (hparameter : IsMaximalTorusParameter j₀ q)
    (U : Over (Spec (CommRingCat.of k))) (g h : U ⟶ G.X) :
    g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (torusNormalizer j₀).carrier U :=
  hparameter.2.2.1 U g h

/-- The same parameter map has the published ground-field torus compatibility. -/
theorem conjugationCompatible (h : IsMaximalTorusParameter j₀ q) :
    TorusParameterConjugationCompatible j₀ q :=
  h.2.2.2

end IsMaximalTorusParameter

end Langlands.GroupScheme
