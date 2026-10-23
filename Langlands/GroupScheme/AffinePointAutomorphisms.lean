import Langlands.GroupScheme.CorepresentedPoints

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (G : GroupScheme (Spec (CommRingCat.of R)))

/-- A coefficient algebra automorphism acts on actual affine points by precomposition. -/
def affinePointAut (s : S ≃ₐ[R] S) :
    MulAut ((algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R S)) ⟶ G.X) :=
  (G.points.mapIso ((algSpec (CommRingCat.of R)).mapIso (CommAlgCat.isoMk s).op).op).groupIsoToMulEquiv

/-- The action is pullback along the actual spectrum map of the coefficient automorphism. -/
theorem affinePointAut_apply (s : S ≃ₐ[R] S)
    (x : (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R S)) ⟶ G.X) :
    G.affinePointAut s x =
      (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom s.toAlgHom).op ≫ x := rfl

/-- The identity coefficient automorphism fixes every point. -/
@[simp] theorem affinePointAut_one : G.affinePointAut (1 : S ≃ₐ[R] S) = 1 := by
  apply MulEquiv.ext
  intro x
  rw [affinePointAut_apply]
  change (algSpec (CommRingCat.of R)).map (𝟙 _) ≫ x = x
  simp

/-- Composition of coefficient automorphisms has the same order as composition of point actions. -/
theorem affinePointAut_mul (s t : S ≃ₐ[R] S) :
    G.affinePointAut (s * t) = G.affinePointAut s * G.affinePointAut t := by
  apply MulEquiv.ext
  intro x
  change G.affinePointAut (s * t) x = G.affinePointAut s (G.affinePointAut t x)
  rw [G.affinePointAut_apply (s * t), G.affinePointAut_apply s,
    G.affinePointAut_apply t, ← Category.assoc, ← Functor.map_comp]
  rfl

/-- The actual action of coefficient automorphisms on affine points, as a group homomorphism. -/
def affinePointAutHom : (S ≃ₐ[R] S) →* MulAut
    ((algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R S)) ⟶ G.X) where
  toFun := G.affinePointAut
  map_one' := G.affinePointAut_one
  map_mul' := G.affinePointAut_mul

/-- Equivariant coefficient maps give equivariant pullbacks of actual affine points. -/
theorem affinePointAut_naturality {T : Type u} [CommRing T] [Algebra R T]
    (s : S ≃ₐ[R] S) (t : T ≃ₐ[R] T) (f : S →ₐ[R] T)
    (h : t.toAlgHom.comp f = f.comp s.toAlgHom)
    (x : (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R S)) ⟶ G.X) :
    G.affinePointAut t ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op ≫ x) =
      (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op ≫ G.affinePointAut s x := by
  rw [G.affinePointAut_apply t, G.affinePointAut_apply s,
    ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun k : S →ₐ[R] T =>
    (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom k).op ≫ x) h

/-- Morphisms of group schemes defined over R commute with the coefficient action. -/
theorem affinePointAut_target {H : GroupScheme (Spec (CommRingCat.of R))}
    (f : G ⟶ H) (s : S ≃ₐ[R] S)
    (x : (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R S)) ⟶ G.X) :
    H.affinePointAut s (x ≫ f.hom.hom) = G.affinePointAut s x ≫ f.hom.hom := by
  rw [H.affinePointAut_apply, G.affinePointAut_apply, Category.assoc]

end Langlands.GroupScheme
