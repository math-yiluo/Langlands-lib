import Langlands.GroupScheme.Reductive.WeilFactorAlgebraRecovery
import Langlands.GroupScheme.AffinePointBaseChangeSmooth
import Langlands.GroupScheme.AffineWeilEmbeddingProductMaps
import Langlands.GroupScheme.AffinePointComparison
import Langlands.GroupScheme.SimplyConnected.Basic

/-! # Uniqueness of the Weil restriction description, from factor rigidity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.WeilFactor

open Langlands.Algebra.GraphIdempotent

section Restriction

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- A `B`-algebra regarded as an `A`-algebra. -/
abbrev resA : CommAlgCat.{u} (CommRingCat.of B) ⥤ CommAlgCat.{u} (CommRingCat.of A) where
  obj X :=
    letI : Algebra A X := Algebra.compHom X (algebraMap A B)
    CommAlgCat.of (CommRingCat.of A) X
  map {X Y} f :=
    letI : Algebra A X := Algebra.compHom X (algebraMap A B)
    letI : Algebra A Y := Algebra.compHom Y (algebraMap A B)
    CommAlgCat.ofHom
      { f.hom.toRingHom with commutes' := fun a => f.hom.commutes (algebraMap A B a) }
  map_id _ := rfl
  map_comp _ _ := rfl

variable {A B}

variable (A) in
/-- The structure map `B → X` as an `A`-algebra map into `resA X`. -/
def structureMap (X : CommAlgCat.{u} (CommRingCat.of B)) : B →ₐ[A] (resA A B).obj X where
  toRingHom := algebraMap B X
  commutes' _ := rfl

variable (A) in
/-- The multiplication `B ⊗_A X → X`, `b ⊗ x ↦ b x`, as a `B`-algebra map. -/
def mulMap (X : CommAlgCat.{u} (CommRingCat.of B)) : B ⊗[A] (resA A B).obj X →ₐ[B] X :=
  { (graphMul (structureMap A X)).toRingHom with
    commutes' := fun b => by
      change graphMul (structureMap A X) (b ⊗ₜ[A] 1) = algebraMap B X b
      rw [Algebra.TensorProduct.productMap_apply_tmul, AlgHom.id_apply, mul_one]
      rfl }

theorem mulMap_apply (X : CommAlgCat.{u} (CommRingCat.of B)) (x : B ⊗[A] (resA A B).obj X) :
    mulMap A X x = graphMul (structureMap A X) x := rfl

theorem mulMap_surjective (X : CommAlgCat.{u} (CommRingCat.of B)) :
    Function.Surjective (mulMap A X) := fun x =>
  ⟨(1 : B) ⊗ₜ[A] x, by
    rw [mulMap_apply, Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
    rfl⟩

theorem ker_mulMap {X : CommAlgCat.{u} (CommRingCat.of B)} {e : B ⊗[A] (resA A B).obj X}
    (he : IsGraphIdempotent (structureMap A X) e) :
    RingHom.ker (mulMap A X) = Ideal.span {1 - e} := by
  ext x
  rw [RingHom.mem_ker]
  constructor
  · intro hx
    have h := he.mul_eq x
    rw [← mulMap_apply, hx, TensorProduct.tmul_zero, zero_mul] at h
    exact Ideal.mem_span_singleton'.mpr ⟨x, by rw [mul_sub, mul_one, h, sub_zero]⟩
  · intro hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    change mulMap A X (c * (1 - e)) = 0
    rw [map_mul, map_sub, map_one, mulMap_apply (A := A) X e, he.graphMul_eq_one, sub_self, mul_zero]

end Restriction

section Embedding

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]

variable (A) in
/-- The graph idempotent of the structure map `B → X`. -/
def graphIdem (X : CommAlgCat.{u} (CommRingCat.of B)) : B ⊗[A] (resA A B).obj X :=
  Classical.choose (exists_isGraphIdempotent (A := A) (B := B) (T := (resA A B).obj X)
    (structureMap A X))

theorem graphIdem_spec (X : CommAlgCat.{u} (CommRingCat.of B)) :
    IsGraphIdempotent (structureMap A X) (graphIdem A X) :=
  Classical.choose_spec (exists_isGraphIdempotent (A := A) (B := B) (T := (resA A B).obj X)
    (structureMap A X))

theorem graphIdem_map {X Y : CommAlgCat.{u} (CommRingCat.of B)} (f : X ⟶ Y) :
    lT ((resA A B).map f) (graphIdem A X) = graphIdem A Y := by
  rw [lT_apply]
  have h := (graphIdem_spec (A := A) X).map ((resA A B).map f).hom
  refine h.unique ?_
  have hc : ((resA A B).map f).hom.comp (structureMap A X) = structureMap A Y := by
    ext b
    exact f.hom.commutes b
  rw [hc]
  exact graphIdem_spec Y

end Embedding

section EmbeddingPoints

open IdempotentPoints

theorem snd_map_eq_one {R C C' : Type u} [CommRing R] [CommRing C] [Algebra R C] [CommRing C']
    [Algebra R C'] (K : GroupScheme (Spec (CommRingCat.of R))) [IsAffine K.X.left]
    (f : C →ₐ[R] C') {e : C} (he : IsIdempotentElem e)
    {k : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)} (hk : snd K e k = 1) :
    snd K (f e) (K.affinePointMap (CommAlgCat.ofHom f) k) = 1 := by
  have hk' : k = proj K e k := (eq_proj_iff K he).mpr ⟨rfl, hk⟩
  rw [hk', proj_map K f he rfl]
  exact snd_proj K (he.map f) _

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
  [Module.Projective A B] [Algebra.Etale A B]
  (G : GroupScheme (Spec (CommRingCat.of B))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

omit [Module.Finite A B] [Module.Projective A B] [Algebra.Etale A B] in
theorem mulMap_comp_lTensor {X Y : CommAlgCat.{u} (CommRingCat.of B)} (f : X ⟶ Y) :
    (mulMap A Y).comp (Algebra.TensorProduct.lTensor (S := B) B ((resA A B).map f).hom) =
      f.hom.comp (mulMap A X) := by
  ext x
  induction x with
  | tmul b x =>
    change graphMul (structureMap A Y) (b ⊗ₜ[A] f.hom x) =
      f.hom (graphMul (structureMap A X) (b ⊗ₜ[A] x))
    rw [Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.productMap_apply_tmul,
      AlgHom.id_apply, AlgHom.id_apply]
    change algebraMap B Y b * f.hom x = f.hom (algebraMap B X b * x)
    rw [map_mul, f.hom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (A) in
/-- The points of `G` over `X` as the factor of `G(B ⊗ X)` cut out by the graph idempotent. -/
abbrev factorEquivX (X : CommAlgCat.{u} (CommRingCat.of B)) :
    (snd G (graphIdem A X)).ker ≃* G.affinePoints (CommAlgCat.of (CommRingCat.of B) X) :=
  factorEquiv G (graphIdem_spec (A := A) X).isIdempotentElem (mulMap_surjective (A := A) X)
    (ker_mulMap (graphIdem_spec X))

omit [Module.Finite A B] [Module.Projective A B] [LocallyOfFiniteType G.X.hom] in
theorem factorEquivX_symm_natural {X Y : CommAlgCat.{u} (CommRingCat.of B)} (f : X ⟶ Y)
    (g : G.affinePoints (CommAlgCat.of (CommRingCat.of B) X)) :
    ((factorEquivX A G Y).symm (G.affinePointMap (CommAlgCat.ofHom f.hom) g)).1 =
      G.affinePointMap (CommAlgCat.ofHom
        (Algebra.TensorProduct.lTensor (S := B) B ((resA A B).map f).hom))
          ((factorEquivX A G X).symm g).1 := by
  set k := (factorEquivX A G X).symm g with hkdef
  have hmem : G.affinePointMap (CommAlgCat.ofHom
      (Algebra.TensorProduct.lTensor (S := B) B ((resA A B).map f).hom)) k.1 ∈
        (snd G (graphIdem A Y)).ker := by
    have h1 := snd_map_eq_one G
      (Algebra.TensorProduct.lTensor (S := B) B ((resA A B).map f).hom)
      (graphIdem_spec (A := A) X).isIdempotentElem k.2
    have h2 : Algebra.TensorProduct.lTensor (S := B) B ((resA A B).map f).hom (graphIdem A X) =
        graphIdem A Y := graphIdem_map f
    rw [h2] at h1
    exact h1
  have hk : (factorEquivX A G Y) ⟨_, hmem⟩ = G.affinePointMap (CommAlgCat.ofHom f.hom) g := by
    have hg : g = (factorEquivX A G X) k := ((factorEquivX A G X).apply_symm_apply g).symm
    apply ev_injective G
    intro a
    rw [factorEquiv_apply, ev_map, ev_map, hg, factorEquiv_apply, ev_map, ev_map]
    exact congrArg (fun φ : B ⊗[A] (resA A B).obj X →ₐ[B] Y => φ (ev G k.1 a))
      (mulMap_comp_lTensor f)
  rw [← hk, MulEquiv.symm_apply_apply]

variable (A) in
/-- Points of `G` over a `B`-algebra `X` embedded into the points of `R_{B/A}(G)` over `X`, as the
points fixed by the factor projection of the graph idempotent. -/
def embNat : G.affinePointFunctor ⟶ resA A B ⋙ (AffineWeil.groupScheme A B G).affinePointFunctor where
  app X := GrpCat.ofHom ((((AffineWeil.pointsEquiv A B G ((resA A B).obj X)).symm.toMonoidHom).comp
    (snd G (graphIdem A X)).ker.subtype).comp (factorEquivX A G X).symm.toMonoidHom)
  naturality X Y f := by
    refine GrpCat.ext ?_
    intro (g : G.affinePoints (CommAlgCat.of (CommRingCat.of B) X))
    change (AffineWeil.pointsEquiv A B G ((resA A B).obj Y)).symm
          ((factorEquivX A G Y).symm (G.affinePointMap (CommAlgCat.ofHom f.hom) g)).1 =
        (AffineWeil.groupScheme A B G).affinePointMap (CommAlgCat.ofHom ((resA A B).map f).hom)
          ((AffineWeil.pointsEquiv A B G ((resA A B).obj X)).symm
            ((factorEquivX A G X).symm g).1)
    apply (AffineWeil.pointsEquiv A B G ((resA A B).obj Y)).injective
    rw [MulEquiv.apply_symm_apply, AffineWeil.pointsEquiv_naturality, MulEquiv.apply_symm_apply]
    exact factorEquivX_symm_natural G f g

omit [Module.Finite A B] [Module.Projective A B] [Algebra.Etale A B] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] in
theorem mulMap_points_natural [IsAffine G.X.left] {X Y : CommAlgCat.{u} (CommRingCat.of B)}
    (f : X ⟶ Y) (k : G.affinePoints (CommAlgCat.of (CommRingCat.of B) (B ⊗[A] (resA A B).obj X))) :
    G.affinePointMap (CommAlgCat.ofHom (mulMap A Y))
        (G.affinePointMap (CommAlgCat.ofHom
          (Algebra.TensorProduct.lTensor (S := B) B ((resA A B).map f).hom)) k) =
      G.affinePointMap (CommAlgCat.ofHom f.hom) (G.affinePointMap (CommAlgCat.ofHom (mulMap A X)) k) := by
  apply ev_injective G
  intro a
  rw [ev_map, ev_map, ev_map, ev_map]
  exact congrArg (fun φ : B ⊗[A] (resA A B).obj X →ₐ[B] Y => φ (ev G k a)) (mulMap_comp_lTensor f)

variable (A) in
/-- The projection `R_{B/A}(G)(X) = G(B ⊗ X) → G(X)` along the multiplication `B ⊗ X → X`. -/
def projNat : resA A B ⋙ (AffineWeil.groupScheme A B G).affinePointFunctor ⟶ G.affinePointFunctor where
  app X := GrpCat.ofHom ((G.affinePointMap (CommAlgCat.ofHom (mulMap A X))).comp
    (AffineWeil.pointsEquiv A B G ((resA A B).obj X)).toMonoidHom)
  naturality X Y f := by
    refine GrpCat.ext ?_
    intro (h : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) ((resA A B).obj X)))
    change G.affinePointMap (CommAlgCat.ofHom (mulMap A Y))
        (AffineWeil.pointsEquiv A B G ((resA A B).obj Y)
          ((AffineWeil.groupScheme A B G).affinePointMap
            (CommAlgCat.ofHom ((resA A B).map f).hom) h)) =
      G.affinePointMap (CommAlgCat.ofHom f.hom) (G.affinePointMap (CommAlgCat.ofHom (mulMap A X))
        (AffineWeil.pointsEquiv A B G ((resA A B).obj X) h))
    rw [AffineWeil.pointsEquiv_naturality]
    exact mulMap_points_natural G f _

theorem embNat_projNat : embNat A G ≫ projNat A G = 𝟙 _ := by
  refine NatTrans.ext (funext fun X => GrpCat.ext ?_)
  intro (g : G.affinePoints (CommAlgCat.of (CommRingCat.of B) X))
  change G.affinePointMap (CommAlgCat.ofHom (mulMap A X))
      (AffineWeil.pointsEquiv A B G ((resA A B).obj X)
        ((AffineWeil.pointsEquiv A B G ((resA A B).obj X)).symm
          ((factorEquivX A G X).symm g).1)) = g
  rw [MulEquiv.apply_symm_apply]
  exact (factorEquivX A G X).apply_symm_apply g

theorem embNat_projNat_of_snd (X : CommAlgCat.{u} (CommRingCat.of B))
    (h : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) ((resA A B).obj X)))
    (hfix : snd G (graphIdem A X) (AffineWeil.pointsEquiv A B G ((resA A B).obj X) h) = 1) :
    ((embNat A G).app X).hom (((projNat A G).app X).hom h) = h := by
  change (AffineWeil.pointsEquiv A B G ((resA A B).obj X)).symm
      ((factorEquivX A G X).symm (G.affinePointMap (CommAlgCat.ofHom (mulMap A X))
        (AffineWeil.pointsEquiv A B G ((resA A B).obj X) h))).1 = h
  apply (AffineWeil.pointsEquiv A B G ((resA A B).obj X)).injective
  rw [MulEquiv.apply_symm_apply]
  have hk : G.affinePointMap (CommAlgCat.ofHom (mulMap A X))
      (AffineWeil.pointsEquiv A B G ((resA A B).obj X) h) =
        factorEquivX A G X ⟨AffineWeil.pointsEquiv A B G ((resA A B).obj X) h, hfix⟩ := rfl
  rw [hk, MulEquiv.symm_apply_apply]

theorem projNat_embNat_apply (X : CommAlgCat.{u} (CommRingCat.of B))
    (g : G.affinePoints (CommAlgCat.of (CommRingCat.of B) X)) :
    ((projNat A G).app X).hom (((embNat A G).app X).hom g) = g := by
  change G.affinePointMap (CommAlgCat.ofHom (mulMap A X))
      (AffineWeil.pointsEquiv A B G ((resA A B).obj X)
        ((AffineWeil.pointsEquiv A B G ((resA A B).obj X)).symm
          ((factorEquivX A G X).symm g).1)) = g
  rw [MulEquiv.apply_symm_apply]
  exact (factorEquivX A G X).apply_symm_apply g

end EmbeddingPoints

section Fixed

open IdempotentPoints

variable {A B B'' : Type u} [CommRing A] [CommRing B] [CommRing B''] [Algebra A B]
  [Algebra A B''] [Module.Finite A B] [Module.Projective A B] [Module.Finite A B'']
  [Module.Projective A B''] [Algebra.Etale A B'']
  {G : GroupScheme (Spec (CommRingCat.of B))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {G'' : GroupScheme (Spec (CommRingCat.of B''))} [IsAffine G''.X.left]
  [LocallyOfFiniteType G''.X.hom]
  (Φ : AffineWeil.groupScheme A B G ≅ AffineWeil.groupScheme A B'' G'')
  (hR : WeilFactorIdempotentRigidityStatement.{u})
  (hred'' : IsReductive G'') (hsimple'' : ∀ s, IsAlmostSimple (geometricFiber G'' s))

omit [Module.Finite A B] [Module.Projective A B] in
theorem baseIdem_id {T : CommAlgCat.{u} (CommRingCat.of A)} (e : B ⊗[A] T) :
    baseIdem (Under.mk (𝟙 T)) e = e := by
  change Algebra.TensorProduct.lTensor (S := B) B (AlgHom.id A T) e = e
  induction e with
  | tmul b t => rfl
  | add x y hx hy => rw [map_add, hx, hy]

/-- An isomorphism of Weil restrictions carries points in the `e`-factor to points in the
`transfer e`-factor. -/
theorem snd_transfer_of_snd {T : CommAlgCat.{u} (CommRingCat.of A)} {e : B ⊗[A] T}
    (he : IsIdempotentElem e)
    (x : (AffineWeil.groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) T))
    (hx : snd G e (AffineWeil.pointsEquiv A B G T x) = 1) :
    snd G'' (transfer Φ hR hred'' hsimple'' e)
      (AffineWeil.pointsEquiv A B'' G'' T
        ((AffineWeil.groupScheme A B G).affinePointsTarget Φ.hom _ x)) = 1 := by
  set X0 : Under T := Under.mk (𝟙 T)
  have he'' := transfer_isIdempotentElem Φ hR hred'' hsimple'' he
  have hfix : pt (factorProjection A B G e he) X0 x = x := by
    apply (AffineWeil.pointsEquiv A B G T).injective
    refine (pointsEquiv_pt_factorProjection (G := G) he X0 x).trans ?_
    have hb : baseIdem X0 e = e := baseIdem_id e
    erw [hb]
    exact ((eq_proj_iff G he).mpr ⟨rfl, hx⟩).symm
  have hid : ∀ y : (AffineWeil.groupScheme A B'' G'').affinePoints
      (CommAlgCat.of (CommRingCat.of A) T),
      (AffineWeil.groupScheme A B G).affinePointsTarget Φ.hom _
        ((AffineWeil.groupScheme A B'' G'').affinePointsTarget Φ.inv _ y) = y := fun y =>
    congrArg (fun ν => pt ν X0 y) (transportNat_inv_hom Φ (T := T))
  have hhi : (AffineWeil.groupScheme A B'' G'').affinePointsTarget Φ.inv _
      ((AffineWeil.groupScheme A B G).affinePointsTarget Φ.hom _ x) = x :=
    congrArg (fun ν => pt ν X0 x) (transportNat_hom_inv Φ (T := T))
  have hfix'' : pt (factorProjection A B'' G'' (transfer Φ hR hred'' hsimple'' e) he'') X0
      ((AffineWeil.groupScheme A B G).affinePointsTarget Φ.hom _ x) =
        (AffineWeil.groupScheme A B G).affinePointsTarget Φ.hom _ x := by
    rw [factorProjection_transfer Φ hR hred'' hsimple'' he, pt_conj]
    erw [hhi, hfix]
    rfl
  have h1 := (pointsEquiv_pt_factorProjection (G := G'') he'' X0
    ((AffineWeil.groupScheme A B G).affinePointsTarget Φ.hom _ x)).symm.trans
      (congrArg (AffineWeil.pointsEquiv A B'' G'' T) hfix'')
  have hb'' : baseIdem X0 (transfer Φ hR hred'' hsimple'' e) = transfer Φ hR hred'' hsimple'' e :=
    baseIdem_id _
  erw [hb''] at h1
  rw [← h1]
  exact snd_proj G'' he'' _

end Fixed

section Alpha

variable {A B B'' : Type u} [CommRing A] [CommRing B] [CommRing B''] [Algebra A B]
  [Algebra A B''] (α : B'' ≃ₐ[A] B)

/-- A `B`-algebra regarded as a `B''`-algebra through `α : B'' ≃ B`. -/
abbrev resAlpha : CommAlgCat.{u} (CommRingCat.of B) ⥤ CommAlgCat.{u} (CommRingCat.of B'') where
  obj X :=
    letI : Algebra B'' X := Algebra.compHom X (α : B'' →+* B)
    CommAlgCat.of (CommRingCat.of B'') X
  map {X Y} f :=
    letI : Algebra B'' X := Algebra.compHom X (α : B'' →+* B)
    letI : Algebra B'' Y := Algebra.compHom Y (α : B'' →+* B)
    CommAlgCat.ofHom { f.hom.toRingHom with commutes' := fun b => f.hom.commutes (α b) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The identity of a `B`-algebra, from the `A`-structure through `B` to the one through `α`. -/
def resIsoHom (X : CommAlgCat.{u} (CommRingCat.of B)) :
    ((resA A B).obj X : Type u) →ₐ[A] ((resA A B'').obj ((resAlpha α).obj X) : Type u) :=
  { RingHom.id X with
    commutes' := fun a => by
      change algebraMap B X (algebraMap A B a) = algebraMap B X (α (algebraMap A B'' a))
      rw [α.commutes] }

/-- The identity of a `B`-algebra, from the `A`-structure through `α` to the one through `B`. -/
def resIsoInv (X : CommAlgCat.{u} (CommRingCat.of B)) :
    ((resA A B'').obj ((resAlpha α).obj X) : Type u) →ₐ[A] ((resA A B).obj X : Type u) :=
  { RingHom.id X with
    commutes' := fun a => by
      change algebraMap B X (α (algebraMap A B'' a)) = algebraMap B X (algebraMap A B a)
      rw [α.commutes] }

set_option linter.internalConstructors false in
/-- The two `A`-algebra structures on a `B`-algebra, through `B` and through `α`, agree. -/
def resIso : resA A B ≅ resAlpha α ⋙ resA A B'' :=
  NatIso.ofComponents (fun X =>
    { hom := ⟨resIsoHom α X⟩
      inv := ⟨resIsoInv α X⟩
      hom_inv_id := rfl
      inv_hom_id := rfl })
    (fun _ => rfl)

theorem resIso_hom_app_hom (X : CommAlgCat.{u} (CommRingCat.of B)) :
    ((resIso α).hom.app X).hom = resIsoHom α X := rfl

end Alpha

section BaseChange

open CategoryTheory.Limits

variable {A B B'' : Type u} [CommRing A] [CommRing B] [CommRing B''] [Algebra A B]
  [Algebra A B''] (α : B'' ≃ₐ[A] B) (G'' : GroupScheme (Spec (CommRingCat.of B'')))

/-- The base change of `G''` along `Spec α : Spec B → Spec B''`. -/
abbrev baseChangeAlpha : GroupScheme (Spec (CommRingCat.of B)) :=
  (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (α : B'' →+* B)))).obj G''

/-- Points of the base change over a `B`-algebra `X` are points of `G''` over `X` viewed as a
`B''`-algebra through `α`. -/
def bcEquiv (X : CommAlgCat.{u} (CommRingCat.of B)) :
    G''.affinePoints ((resAlpha α).obj X) ≃* (baseChangeAlpha α G'').affinePoints X :=
  letI : Algebra B'' B := (α : B'' →+* B).toAlgebra
  letI : Algebra B'' X := Algebra.compHom X (α : B'' →+* B)
  haveI : IsScalarTower B'' B X := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  affinePointsBaseChangeMulEquiv B'' B X G''

theorem bcEquiv_symm_left (X : CommAlgCat.{u} (CommRingCat.of B))
    (q : (baseChangeAlpha α G'').affinePoints X) :
    ((bcEquiv α G'' X).symm q).left =
      q.left ≫ pullback.fst G''.X.hom (Spec.map (CommRingCat.ofHom (α : B'' →+* B))) := by
  let _ : Algebra B'' B := (α : B'' →+* B).toAlgebra
  let _ : Algebra B'' X := Algebra.compHom X (α : B'' →+* B)
  have _ : IsScalarTower B'' B X := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact affinePointsBaseChangeMulEquiv_symm_left B'' B X G'' q

/-- The base-change comparison as a natural transformation. -/
def bcNat : resAlpha α ⋙ G''.affinePointFunctor ⟶ (baseChangeAlpha α G'').affinePointFunctor where
  app X := GrpCat.ofHom (bcEquiv α G'' X).toMonoidHom
  naturality X Y f := by
    refine GrpCat.ext ?_
    intro (g : G''.affinePoints ((resAlpha α).obj X))
    change bcEquiv α G'' Y (G''.affinePointMap ((resAlpha α).map f) g) =
      (baseChangeAlpha α G'').affinePointMap f (bcEquiv α G'' X g)
    apply (bcEquiv α G'' Y).symm.injective
    rw [MulEquiv.symm_apply_apply]
    apply Over.OverMorphism.ext
    have h1 := bcEquiv_symm_left α G'' Y ((baseChangeAlpha α G'').affinePointMap f
      (bcEquiv α G'' X g))
    have h2 := bcEquiv_symm_left α G'' X (bcEquiv α G'' X g)
    rw [MulEquiv.symm_apply_apply] at h2
    rw [h1, affinePointMap_apply, Over.comp_left]
    erw [Category.assoc, ← h2]
    rfl

/-- The inverse base-change comparison. -/
def bcNatInv : (baseChangeAlpha α G'').affinePointFunctor ⟶ resAlpha α ⋙ G''.affinePointFunctor where
  app X := GrpCat.ofHom (bcEquiv α G'' X).symm.toMonoidHom
  naturality X Y f := by
    refine GrpCat.ext ?_
    intro (q : (baseChangeAlpha α G'').affinePoints X)
    change (bcEquiv α G'' Y).symm ((baseChangeAlpha α G'').affinePointMap f q) =
      G''.affinePointMap ((resAlpha α).map f) ((bcEquiv α G'' X).symm q)
    apply (bcEquiv α G'' Y).injective
    rw [MulEquiv.apply_symm_apply]
    have h := ConcreteCategory.congr_hom ((bcNat α G'').naturality f) ((bcEquiv α G'' X).symm q)
    change bcEquiv α G'' Y (G''.affinePointMap ((resAlpha α).map f) ((bcEquiv α G'' X).symm q)) =
      (baseChangeAlpha α G'').affinePointMap f (bcEquiv α G'' X ((bcEquiv α G'' X).symm q)) at h
    rw [h, MulEquiv.apply_symm_apply]

/-- The base-change comparison as a natural isomorphism. -/
def bcIso : resAlpha α ⋙ G''.affinePointFunctor ≅ (baseChangeAlpha α G'').affinePointFunctor where
  hom := bcNat α G''
  inv := bcNatInv α G''
  hom_inv_id := by
    refine NatTrans.ext (funext fun X => GrpCat.ext ?_)
    intro (g : G''.affinePoints ((resAlpha α).obj X))
    exact (bcEquiv α G'' X).symm_apply_apply g
  inv_hom_id := by
    refine NatTrans.ext (funext fun X => GrpCat.ext ?_)
    intro (q : (baseChangeAlpha α G'').affinePoints X)
    exact (bcEquiv α G'' X).apply_symm_apply q

end BaseChange

section Assembly

open IdempotentPoints

/-- A homomorphism of group schemes acting on affine points. -/
abbrev apfMap {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)} (f : G ⟶ H) :
    G.affinePointFunctor ⟶ H.affinePointFunctor :=
  Functor.whiskerLeft (algSpec R).rightOp (pointsMap f)

variable {A B B'' : Type u} [CommRing A] [CommRing B] [CommRing B''] [Algebra A B]
  [Algebra A B''] [Module.Finite A B] [Module.Projective A B] [Module.Finite A B'']
  [Module.Projective A B''] [Algebra.Etale A B] [Algebra.Etale A B'']
  {G : GroupScheme (Spec (CommRingCat.of B))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {G'' : GroupScheme (Spec (CommRingCat.of B''))} [IsAffine G''.X.left]
  [LocallyOfFiniteType G''.X.hom]
  (Φ : AffineWeil.groupScheme A B G ≅ AffineWeil.groupScheme A B'' G'')
  (hR : WeilFactorIdempotentRigidityStatement.{u})
  (hred'' : IsReductive G'') (hsimple'' : ∀ s, IsAlmostSimple (geometricFiber G'' s))
  (α : B'' ≃ₐ[A] B)
  (hα : ∀ (T : CommAlgCat.{u} (CommRingCat.of A)) (φ : B →ₐ[A] T) (e : B ⊗[A] T),
    IsGraphIdempotent φ e →
      IsGraphIdempotent (φ.comp (α : B'' →ₐ[A] B)) (transfer Φ hR hred'' hsimple'' e))

include hα in
theorem graphIdem_transfer (X : CommAlgCat.{u} (CommRingCat.of B)) :
    lT ((resIso α).hom.app X) (transfer Φ hR hred'' hsimple'' (graphIdem A X)) =
      graphIdem A ((resAlpha α).obj X) := by
  have h := (hα ((resA A B).obj X) (structureMap A X) (graphIdem A X) (graphIdem_spec X)).map
    ((resIso α).hom.app X).hom
  rw [lT_apply]
  refine h.unique ?_
  have hc : ((resIso α).hom.app X).hom.comp ((structureMap A X).comp (α : B'' →ₐ[A] B)) =
      structureMap A ((resAlpha α).obj X) := by
    ext b
    rfl
  rw [hc]
  exact graphIdem_spec _


/-- The comparison `G ⟶ G''_α` on affine points: embed into the Weil restriction, transport by
`Φ`, and project. -/
def fwdNat : G.affinePointFunctor ⟶ (baseChangeAlpha α G'').affinePointFunctor :=
  embNat A G ≫ Functor.whiskerLeft (resA A B) (apfMap Φ.hom) ≫
    Functor.whiskerRight (resIso α).hom (AffineWeil.groupScheme A B'' G'').affinePointFunctor ≫
    Functor.whiskerLeft (resAlpha α) (projNat A G'') ≫ (bcIso α G'').hom

/-- The comparison `G''_α ⟶ G` on affine points. -/
def bwdNat : (baseChangeAlpha α G'').affinePointFunctor ⟶ G.affinePointFunctor :=
  (bcIso α G'').inv ≫ Functor.whiskerLeft (resAlpha α) (embNat A G'') ≫
    Functor.whiskerRight (resIso α).inv (AffineWeil.groupScheme A B'' G'').affinePointFunctor ≫
    Functor.whiskerLeft (resA A B) (apfMap Φ.inv) ≫ projNat A G

omit [Algebra.Etale A B] in
theorem affinePointMap_inv_hom {R : CommRingCat.{u}} (K : GroupScheme (Spec R))
    {S S' : CommAlgCat.{u} R} (i : S ≅ S') (z : K.affinePoints S) :
    K.affinePointMap i.inv (K.affinePointMap i.hom z) = z := by
  rw [← MonoidHom.comp_apply, ← affinePointMap_comp, Iso.hom_inv_id, affinePointMap_id]
  rfl

set_option maxRecDepth 20000 in
include hα in
theorem fwdNat_bwdNat : fwdNat Φ α ≫ bwdNat Φ α = 𝟙 _ := by
  refine NatTrans.ext (funext fun X => GrpCat.ext ?_)
  intro (g : G.affinePoints (CommAlgCat.of (CommRingCat.of B) X))
  let x := ((embNat A G).app X).hom g
  have hx : snd G (graphIdem A X) (AffineWeil.pointsEquiv A B G ((resA A B).obj X) x) = 1 := by
    change snd G _ (AffineWeil.pointsEquiv A B G ((resA A B).obj X)
      ((AffineWeil.pointsEquiv A B G ((resA A B).obj X)).symm
        ((factorEquivX A G X).symm g).1)) = 1
    rw [MulEquiv.apply_symm_apply]
    exact ((factorEquivX A G X).symm g).2
  let Φx := (AffineWeil.groupScheme A B G).affinePointsTarget Φ.hom _ x
  have he'' := transfer_isIdempotentElem Φ hR hred'' hsimple''
    (graphIdem_spec (A := A) X).isIdempotentElem
  have h1 := snd_transfer_of_snd Φ hR hred'' hsimple''
    (graphIdem_spec (A := A) X).isIdempotentElem x hx
  let y := (AffineWeil.groupScheme A B'' G'').affinePointMap ((resIso α).hom.app X) Φx
  have hy : snd G'' (graphIdem A ((resAlpha α).obj X))
      (AffineWeil.pointsEquiv A B'' G'' ((resA A B'').obj ((resAlpha α).obj X)) y) = 1 := by
    have hn := AffineWeil.pointsEquiv_naturality A B'' G'' ((resIso α).hom.app X).hom Φx
    change AffineWeil.pointsEquiv A B'' G'' ((resA A B'').obj ((resAlpha α).obj X)) y = _ at hn
    rw [hn, ← graphIdem_transfer Φ hR hred'' hsimple'' α hα X]
    exact snd_map_eq_one G'' _ he'' h1
  have hEP := embNat_projNat_of_snd G'' ((resAlpha α).obj X) y hy
  have hΦ : (AffineWeil.groupScheme A B'' G'').affinePointsTarget Φ.inv _ Φx = x := by
    change (x ≫ Φ.hom.hom.hom) ≫ Φ.inv.hom.hom = x
    have h : Φ.hom.hom.hom ≫ Φ.inv.hom.hom = 𝟙 _ := congrArg (fun f => f.hom.hom) Φ.hom_inv_id
    erw [Category.assoc, h, Category.comp_id]
  have hfin : ((projNat A G).app X).hom x = g := projNat_embNat_apply G X g
  change ((projNat A G).app X).hom ((AffineWeil.groupScheme A B'' G'').affinePointsTarget Φ.inv _
      ((AffineWeil.groupScheme A B'' G'').affinePointMap ((resIso α).inv.app X)
        (((embNat A G'').app ((resAlpha α).obj X)).hom ((bcEquiv α G'' X).symm
          (bcEquiv α G'' X (((projNat A G'').app ((resAlpha α).obj X)).hom y)))))) = g
  erw [MulEquiv.symm_apply_apply, hEP]
  have hinv : (AffineWeil.groupScheme A B'' G'').affinePointMap ((resIso α).inv.app X) y = Φx :=
    affinePointMap_inv_hom _ ((resIso α).app X) Φx
  erw [hinv, hΦ, hfin]

include hα in
theorem graphIdem_transfer_inv (X : CommAlgCat.{u} (CommRingCat.of B)) :
    lT ((resIso α).inv.app X) (graphIdem A ((resAlpha α).obj X)) =
      transfer Φ hR hred'' hsimple'' (graphIdem A X) := by
  rw [← graphIdem_transfer Φ hR hred'' hsimple'' α hα X, lT, lT, lTensor_lTensor]
  generalize transfer Φ hR hred'' hsimple'' (graphIdem A X) = z
  induction z with
  | tmul b t => rfl
  | add x y hx hy => rw [map_add, hx, hy]

set_option maxRecDepth 20000 in
include hα in
theorem bwdNat_fwdNat (hred : IsReductive G) (hsimple : ∀ s, IsAlmostSimple (geometricFiber G s)) :
    bwdNat Φ α ≫ fwdNat Φ α = 𝟙 _ := by
  refine NatTrans.ext (funext fun X => GrpCat.ext ?_)
  intro (q : (baseChangeAlpha α G'').affinePoints X)
  let g'' := (bcEquiv α G'' X).symm q
  let w := ((embNat A G'').app ((resAlpha α).obj X)).hom g''
  have hw : snd G'' (graphIdem A ((resAlpha α).obj X))
      (AffineWeil.pointsEquiv A B'' G'' ((resA A B'').obj ((resAlpha α).obj X)) w) = 1 := by
    change snd G'' _ (AffineWeil.pointsEquiv A B'' G'' ((resA A B'').obj ((resAlpha α).obj X))
      ((AffineWeil.pointsEquiv A B'' G'' ((resA A B'').obj ((resAlpha α).obj X))).symm
        ((factorEquivX A G'' ((resAlpha α).obj X)).symm g'').1)) = 1
    rw [MulEquiv.apply_symm_apply]
    exact ((factorEquivX A G'' ((resAlpha α).obj X)).symm g'').2
  let z := (AffineWeil.groupScheme A B'' G'').affinePointMap ((resIso α).inv.app X) w
  have he := (graphIdem_spec (A := A) X).isIdempotentElem
  have he'' := transfer_isIdempotentElem Φ hR hred'' hsimple'' he
  have hz : snd G'' (transfer Φ hR hred'' hsimple'' (graphIdem A X))
      (AffineWeil.pointsEquiv A B'' G'' ((resA A B).obj X) z) = 1 := by
    have hn := AffineWeil.pointsEquiv_naturality A B'' G'' ((resIso α).inv.app X).hom w
    change AffineWeil.pointsEquiv A B'' G'' ((resA A B).obj X) z = _ at hn
    rw [hn, ← graphIdem_transfer_inv Φ hR hred'' hsimple'' α hα X]
    exact snd_map_eq_one G'' _ (graphIdem_spec _).isIdempotentElem hw
  let u := (AffineWeil.groupScheme A B'' G'').affinePointsTarget Φ.inv _ z
  have hu : snd G (graphIdem A X) (AffineWeil.pointsEquiv A B G ((resA A B).obj X) u) = 1 := by
    have h := snd_transfer_of_snd Φ.symm hR hred hsimple he'' z hz
    rw [transfer_symm_transfer Φ hR hred'' hsimple'' hred hsimple he] at h
    exact h
  have hEP := embNat_projNat_of_snd G X u hu
  have hΦ : (AffineWeil.groupScheme A B G).affinePointsTarget Φ.hom _ u = z := by
    change (z ≫ Φ.inv.hom.hom) ≫ Φ.hom.hom.hom = z
    have h : Φ.inv.hom.hom ≫ Φ.hom.hom.hom = 𝟙 _ := congrArg (fun f => f.hom.hom) Φ.inv_hom_id
    erw [Category.assoc, h, Category.comp_id]
  have hhom : (AffineWeil.groupScheme A B'' G'').affinePointMap ((resIso α).hom.app X) z = w :=
    affinePointMap_inv_hom _ ((resIso α).app X).symm w
  have hfin : ((projNat A G'').app ((resAlpha α).obj X)).hom w = g'' :=
    projNat_embNat_apply G'' ((resAlpha α).obj X) g''
  change bcEquiv α G'' X (((projNat A G'').app ((resAlpha α).obj X)).hom
      ((AffineWeil.groupScheme A B'' G'').affinePointMap ((resIso α).hom.app X)
        ((AffineWeil.groupScheme A B G).affinePointsTarget Φ.hom _
          (((embNat A G).app X).hom (((projNat A G).app X).hom u))))) = q
  erw [hEP, hΦ, hhom, hfin]
  exact (bcEquiv α G'' X).apply_symm_apply q

/-- The isomorphism `G''_α ≅ G` induced by an isomorphism `Φ` of Weil restrictions, for the
algebra isomorphism `α` attached to `Φ` by factor rigidity. -/
def comparisonIso (hred : IsReductive G) (hsimple : ∀ s, IsAlmostSimple (geometricFiber G s)) :
    baseChangeAlpha α G'' ≅ G :=
  (AffinePointComparison.iso
    { hom := fwdNat Φ α
      inv := bwdNat Φ α
      hom_inv_id := fwdNat_bwdNat Φ hR hred'' hsimple'' α hα
      inv_hom_id := bwdNat_fwdNat Φ hR hred'' hsimple'' α hα hred hsimple }).symm

end Assembly

section Main

variable {A B B'' : Type u} [CommRing A] [CommRing B] [CommRing B''] [Algebra A B]
  [Algebra A B''] [Module.Finite A B] [Module.Projective A B] [Module.Finite A B'']
  [Module.Projective A B''] [Algebra.Etale A B] [Algebra.Etale A B'']
  {G : GroupScheme (Spec (CommRingCat.of B))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {G'' : GroupScheme (Spec (CommRingCat.of B''))} [IsAffine G''.X.left]
  [LocallyOfFiniteType G''.X.hom]

/-- **Uniqueness of the Weil restriction description, from factor rigidity.** An isomorphism
`R_{B/A}(G) ≅ R_{B''/A}(G'')` of Weil restrictions of reductive groups with almost simple
geometric fibres yields `α : B'' ≃ B` and an isomorphism from the base change of `G''` along
`Spec α` to `G`. -/
theorem exists_baseChange_iso_of_weilRestriction_iso
    (hR : WeilFactorIdempotentRigidityStatement.{u})
    (hred : IsReductive G) (hsimple : ∀ s, IsAlmostSimple (geometricFiber G s))
    (hred'' : IsReductive G'') (hsimple'' : ∀ s, IsAlmostSimple (geometricFiber G'' s))
    (Φ : AffineWeil.groupScheme A B G ≅ AffineWeil.groupScheme A B'' G'') :
    ∃ α : B'' ≃ₐ[A] B,
      Nonempty ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (α : B'' →+* B)))).obj G'' ≅ G) := by
  obtain ⟨α, hα⟩ := exists_algEquiv_transfer Φ hR hred hsimple hred'' hsimple''
  exact ⟨α, ⟨comparisonIso Φ hR hred'' hsimple'' α hα hred hsimple⟩⟩

/-- The uniqueness clause of `AffineSimplyConnectedWeilRestrictionStatement`, in its exact form,
follows from `WeilFactorIdempotentRigidityStatement`. -/
theorem affineSimplyConnectedWeilRestriction_uniqueness_of_rigidity
    (hR : WeilFactorIdempotentRigidityStatement.{u}) (A : Type u) [CommRing A]
    (G : GroupScheme (Spec (CommRingCat.of A))) :
    ∀ (B B'' : Type u) [CommRing B] [CommRing B''] [Algebra A B] [Algebra A B'']
      [Module.Finite A B] [Module.Finite A B''] [Module.Projective A B]
      [Module.Projective A B''] [Algebra.Etale A B] [Algebra.Etale A B'']
      (G' : GroupScheme (Spec (CommRingCat.of B)))
      (G'' : GroupScheme (Spec (CommRingCat.of B'')))
      [IsAffine G'.X.left] [LocallyOfFiniteType G'.X.hom]
      [IsAffine G''.X.left] [LocallyOfFiniteType G''.X.hom],
      IsReductive G' → IsReductive G'' →
      (∀ s' : Spec (CommRingCat.of B),
        IsSimplyConnected (geometricFiber G' s') ∧ IsAlmostSimple (geometricFiber G' s')) →
      (∀ s'' : Spec (CommRingCat.of B''),
        IsSimplyConnected (geometricFiber G'' s'') ∧ IsAlmostSimple (geometricFiber G'' s'')) →
      Nonempty (G ≅ AffineWeil.groupScheme A B G') →
      Nonempty (G ≅ AffineWeil.groupScheme A B'' G'') →
      ∃ α : B'' ≃ₐ[A] B,
        Nonempty ((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (α : B'' →+* B)))).obj G'' ≅ G') := by
  intro B B'' _ _ _ _ _ _ _ _ _ _ G' G'' _ _ _ _ hred' hred'' h' h'' ⟨e₁⟩ ⟨e₂⟩
  exact exists_baseChange_iso_of_weilRestriction_iso hR hred' (fun s => (h' s).2) hred''
    (fun s => (h'' s).2) (e₁.symm ≪≫ e₂)

end Main

end Langlands.GroupScheme.WeilFactor
