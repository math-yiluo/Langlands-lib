import Langlands.AlgebraicGeometry.PointTopology.AffineFiberProductStatements

/-!
# Proof of the affine fibre-product topology statement

Both components of the fibre-product comparison are composition with `Spec` of a
tensor inclusion, hence continuous. The inverse is continuous because a
tensor-coordinate point is determined, continuously, by its values at `a ⊗ 1` and
`1 ⊗ b`, which are the coordinates of the two factor points.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

namespace AffineFiberProductProof

open _root_.AlgebraicGeometry

section Maps

variable {R A D S : Type u} [CommRing R] [CommRing A] [CommRing D] [CommRing S]
variable [Algebra R A] [Algebra R D] [Algebra R S]

theorem specMap_comp_algebraMap (φ : A →ₐ[R] D) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.algebraMap R A =
      Spec.algebraMap R D := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact φ.commutes r

/-- Composition of an actual scheme point with `Spec` of an algebra map. -/
def comap (φ : A →ₐ[R] D) (q : SpecPoint R D S) : SpecPoint R A S :=
  ⟨q.1 ≫ Spec.map (CommRingCat.ofHom φ.toRingHom), by
    rw [Category.assoc, specMap_comp_algebraMap]
    exact q.2⟩

theorem comap_val (φ : A →ₐ[R] D) (q : SpecPoint R D S) :
    (comap φ q).1 = q.1 ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) := rfl

theorem specPointEquiv_comap (φ : A →ₐ[R] D) (q : SpecPoint R D S) :
    specPointEquiv R A S (comap φ q) = AlgPoint.precomp φ (specPointEquiv R D S q) := by
  have key : CommRingCat.ofHom (specPointEquiv R A S (comap φ q)).toAlgHom.toRingHom =
      CommRingCat.ofHom φ.toRingHom ≫
        CommRingCat.ofHom (specPointEquiv R D S q).toAlgHom.toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    exact (Spec.map_preimage _).trans
      (congrArg (fun k => k ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
        (Spec.map_preimage _)).symm
  ext a
  exact congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of S => f.hom a) key

theorem continuous_comap [TopologicalSpace S] (φ : A →ₐ[R] D) :
    Continuous (comap (S := S) φ) := by
  have h : (comap (S := S) φ) = (specPointHomeomorph R A S).symm ∘
      AlgPoint.precomp φ ∘ specPointHomeomorph R D S := by
    funext q
    change comap φ q = (specPointEquiv R A S).symm
      (AlgPoint.precomp φ (specPointEquiv R D S q))
    rw [Equiv.eq_symm_apply, specPointEquiv_comap]
  rw [h]
  exact (specPointHomeomorph R A S).symm.continuous.comp
    ((AlgPoint.continuous_precomp φ).comp (specPointHomeomorph R D S).continuous)

end Maps

variable (R C A B S : Type u)
variable [CommRing R] [CommRing C] [CommRing A] [CommRing B] [CommRing S]
variable [Algebra R C] [Algebra R A] [Algebra R B] [Algebra R S]
variable [Algebra C A] [Algebra C B] [IsScalarTower R C A] [IsScalarTower R C B]

/-- The left tensor inclusion as an `R`-algebra map. -/
abbrev inclLeft : A →ₐ[R] A ⊗[C] B := Algebra.TensorProduct.includeLeft

/-- The right tensor inclusion as an `R`-algebra map. -/
abbrev inclRight : B →ₐ[R] A ⊗[C] B :=
  (Algebra.TensorProduct.includeRight : B →ₐ[C] A ⊗[C] B).restrictScalars R

/-- The first component of the comparison is composition with `Spec` of the left
tensor inclusion. -/
theorem pair_fst (p : SpecFiberProductPoint R C A B S) :
    (specFiberProductPointPair R C A B S p).1.1 =
      comap (inclLeft R C A B) (specFiberProductTensorEquiv R C A B S p) := by
  apply Subtype.ext
  exact ((Category.assoc p.1 (pullbackSpecIso C A B).hom _).trans
    (congrArg (fun k => p.1 ≫ k) (pullbackSpecIso_hom_fst C A B))).symm

/-- The second component is composition with `Spec` of the right tensor inclusion. -/
theorem pair_snd (p : SpecFiberProductPoint R C A B S) :
    (specFiberProductPointPair R C A B S p).1.2 =
      comap (inclRight R C A B) (specFiberProductTensorEquiv R C A B S p) := by
  apply Subtype.ext
  exact ((Category.assoc p.1 (pullbackSpecIso C A B).hom _).trans
    (congrArg (fun k => p.1 ≫ k) (pullbackSpecIso_hom_snd C A B))).symm

/-- The tensor-coordinate point of a lifted pair, at `a ⊗ 1`, is the coordinate of the
first factor point. -/
theorem lift_tmul_one (pq : CompatibleSpecPointPair R C A B S) (a : A) :
    specPointEquiv R (A ⊗[C] B) S
        (specFiberProductTensorEquiv R C A B S (specFiberProductPointLift R C A B S pq))
        (a ⊗ₜ[C] 1) = specPointEquiv R A S pq.1.1 a := by
  have h := pair_fst R C A B S (specFiberProductPointLift R C A B S pq)
  rw [show specFiberProductPointPair R C A B S (specFiberProductPointLift R C A B S pq) = pq
    from (specFiberProductPointPairEquiv R C A B S).apply_symm_apply pq] at h
  rw [h, specPointEquiv_comap]
  rfl

/-- The tensor-coordinate point of a lifted pair, at `1 ⊗ b`, is the coordinate of the
second factor point. -/
theorem lift_one_tmul (pq : CompatibleSpecPointPair R C A B S) (b : B) :
    specPointEquiv R (A ⊗[C] B) S
        (specFiberProductTensorEquiv R C A B S (specFiberProductPointLift R C A B S pq))
        (1 ⊗ₜ[C] b) = specPointEquiv R B S pq.1.2 b := by
  have h := pair_snd R C A B S (specFiberProductPointLift R C A B S pq)
  rw [show specFiberProductPointPair R C A B S (specFiberProductPointLift R C A B S pq) = pq
    from (specFiberProductPointPairEquiv R C A B S).apply_symm_apply pq] at h
  rw [h, specPointEquiv_comap]
  rfl

variable [TopologicalSpace S]

theorem continuous_pair :
    Continuous (specFiberProductPointPair R C A B S) := by
  apply continuous_induced_rng.2
  have ht : Continuous (specFiberProductTensorEquiv R C A B S) :=
    (specFiberProductTensorHomeomorph R C A B S).continuous
  exact (((continuous_comap _).comp ht).prodMk ((continuous_comap _).comp ht)).congr
    fun p => (Prod.ext (pair_fst R C A B S p) (pair_snd R C A B S p)).symm

theorem continuous_lift [IsTopologicalRing S] :
    Continuous (specFiberProductPointLift R C A B S) := by
  rw [← (specFiberProductTensorHomeomorph R C A B S).comp_continuous_iff,
    ← (specPointHomeomorph R (A ⊗[C] B) S).comp_continuous_iff,
    AlgPoint.continuous_iff]
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    have hfst : Continuous fun pq : CompatibleSpecPointPair R C A B S => pq.1.1 :=
      continuous_fst.comp continuous_subtype_val
    have hsnd : Continuous fun pq : CompatibleSpecPointPair R C A B S => pq.1.2 :=
      continuous_snd.comp continuous_subtype_val
    have ha : Continuous fun pq : CompatibleSpecPointPair R C A B S =>
        specPointEquiv R A S pq.1.1 a :=
      (AlgPoint.continuous_eval a).comp ((specPointHomeomorph R A S).continuous.comp hfst)
    have hb : Continuous fun pq : CompatibleSpecPointPair R C A B S =>
        specPointEquiv R B S pq.1.2 b :=
      (AlgPoint.continuous_eval b).comp ((specPointHomeomorph R B S).continuous.comp hsnd)
    refine (ha.mul hb).congr fun pq => ?_
    have hmul := map_mul (specPointEquiv R (A ⊗[C] B) S (specFiberProductTensorEquiv R C A B S
        (specFiberProductPointLift R C A B S pq))).toAlgHom (a ⊗ₜ[C] (1 : B))
          ((1 : A) ⊗ₜ[C] b)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at hmul
    exact (hmul.trans (congrArg₂ (· * ·) (lift_tmul_one R C A B S pq a)
      (lift_one_tmul R C A B S pq b))).symm
  | add y z hy hz =>
    refine (hy.add hz).congr fun pq => ?_
    exact (map_add (specPointEquiv R (A ⊗[C] B) S (specFiberProductTensorEquiv R C A B S
      (specFiberProductPointLift R C A B S pq))).toAlgHom y z).symm

/-- The fibre-product point comparison, as a homeomorphism. -/
def pairHomeomorph [IsTopologicalRing S] :
    SpecFiberProductPoint R C A B S ≃ₜ CompatibleSpecPointPair R C A B S where
  toEquiv := specFiberProductPointPairEquiv R C A B S
  continuous_toFun := continuous_pair R C A B S
  continuous_invFun := continuous_lift R C A B S

end AffineFiberProductProof

/-- Conrad's Proposition 2.1, fibre products: the actual affine fibre-product point
comparison is a homeomorphism onto compatible pairs. -/
theorem affineFiberProductTopology_proof (R C A B S : Type u)
    [CommRing R] [CommRing C] [CommRing A] [CommRing B] [CommRing S]
    [Algebra R C] [Algebra R A] [Algebra R B] [Algebra R S]
    [Algebra C A] [Algebra C B] [IsScalarTower R C A] [IsScalarTower R C B]
    [TopologicalSpace S] [IsTopologicalRing S] :
    AffineFiberProductTopologyProperty R C A B S :=
  (AffineFiberProductProof.pairHomeomorph R C A B S).isHomeomorph

end Langlands.AlgebraicGeometry.PointTopology
