import Langlands.GroupScheme.IntegralModel.SemilinearExtension
import Langlands.GroupScheme.Descent.SquareTower
import Langlands.GroupScheme.Descent.SemilinearDatum

/-! # Integral semilinear coherence from generic rigidity -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.IntegralModel
open Descent

variable {R L : Type u} [CommRing R] [IsDomain R] [Field L]
  [Algebra R L] [IsFractionRing R L]
  {H : GroupScheme (Spec (CommRingCat.of L))} (N : IntegralModel R L H)

/-- The actual generic semilinear law for an integral pullback isomorphism. -/
def GenericSemilinearCompatible
    (a : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))
    (v : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of L))
    (hvc : v ≫ Spec.algebraMap R L = Spec.algebraMap R L ≫ a)
    (n : (GroupScheme.baseChange a).obj N.group ≅ N.group)
    (e : (GroupScheme.baseChange v).obj H ≅ H) : Prop :=
  (GroupScheme.baseChange v).map N.genericIso.hom ≫ e.hom =
    (squareComparison (Spec.algebraMap R L) v a (Spec.algebraMap R L)
      hvc N.group).hom ≫
        (GroupScheme.baseChange (Spec.algebraMap R L)).map n.hom ≫ N.genericIso.hom

/-- A generic semilinear tower law forces the integral tower law for the
actual flat affine models. -/
theorem semilinear_tower_of_generic
    (a b d : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R)) (hab : a ≫ b = d)
    (v w z : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of L)) (hvw : v ≫ w = z)
    (hvc : v ≫ Spec.algebraMap R L = Spec.algebraMap R L ≫ a)
    (hwc : w ≫ Spec.algebraMap R L = Spec.algebraMap R L ≫ b)
    (hzc : z ≫ Spec.algebraMap R L = Spec.algebraMap R L ≫ d)
    (na : (GroupScheme.baseChange a).obj N.group ≅ N.group)
    (nb : (GroupScheme.baseChange b).obj N.group ≅ N.group)
    (nd : (GroupScheme.baseChange d).obj N.group ≅ N.group)
    (ev : (GroupScheme.baseChange v).obj H ≅ H)
    (ew : (GroupScheme.baseChange w).obj H ≅ H)
    (ez : (GroupScheme.baseChange z).obj H ≅ H)
    (hna : N.GenericSemilinearCompatible a v hvc na ev)
    (hnb : N.GenericSemilinearCompatible b w hwc nb ew)
    (hnd : N.GenericSemilinearCompatible d z hzc nd ez)
    (he : pullbackComparison w v z hvw H ≪≫ ez =
      (GroupScheme.baseChange v).mapIso ew ≪≫ ev) :
    pullbackComparison b a d hab N.group ≪≫ nd =
      (GroupScheme.baseChange a).mapIso nb ≪≫ na := by
  apply Iso.ext
  apply hom_eq_of_generic (M := (N.twist b w hwc).twist a v hvc) (N := N)
  apply (cancel_mono N.genericIso.hom).mp
  apply (cancel_epi
    ((GroupScheme.baseChange v).map
      (squareComparison (Spec.algebraMap R L) w b (Spec.algebraMap R L) hwc N.group).hom ≫
        (squareComparison (Spec.algebraMap R L) v a (Spec.algebraMap R L)
          hvc ((GroupScheme.baseChange b).obj N.group)).hom)).mp
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  have ht := congrArg
    (fun f => f ≫ (GroupScheme.baseChange (Spec.algebraMap R L)).map nd.hom ≫ N.genericIso.hom)
    (squareComparison_tower (Spec.algebraMap R L) a b d hab v w z hvw hvc hwc hzc N.group)
  simp only [Category.assoc] at ht
  rw [ht, ← hnd]
  rw [← pullbackComparison_naturality_assoc w v z hvw N.genericIso.hom]
  have heh := congrArg (fun e => e.hom) he
  simp only [Iso.trans_hom, Functor.mapIso_hom] at heh
  rw [heh]
  have hnb' := congrArg
    (fun f => (GroupScheme.baseChange v).map f ≫ ev.hom) hnb
  simp only [Functor.map_comp, Category.assoc] at hnb'
  rw [hnb', hna]
  rw [squareComparison_naturality_assoc (Spec.algebraMap R L) v a
    (Spec.algebraMap R L) hvc nb.hom]

section Components

variable {B : Scheme.{u}} (p : Spec (CommRingCat.of R) ⟶ B) {I : Type}
  (q : I → (Spec (CommRingCat.of R) ⟶ Overlap p))
  [∀ i, IsIso (q i ≫ fst p)] [Finite I] [IsIso (Sigma.desc q)]
  (a : I → (Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R)))
  (v : I → (Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of L)))
  (hf : ∀ i, q i ≫ fst p = 𝟙 _) (hg : ∀ i, q i ≫ snd p = a i)
  (m : I → I → I) (hm : ∀ i j, a i ≫ a j = a (m i j))
  (hv : ∀ i j, v i ≫ v j = v (m i j))
  (hvc : ∀ i, v i ≫ Spec.algebraMap R L = Spec.algebraMap R L ≫ a i)
  (n : ∀ i, (GroupScheme.baseChange (a i)).obj N.group ≅ N.group)
  (e : ∀ i, (GroupScheme.baseChange (v i)).obj H ≅ H)
  (hn : ∀ i, N.GenericSemilinearCompatible (a i) (v i) (hvc i) (n i) (e i))
  (he : ∀ i j, pullbackComparison (v j) (v i) (v (m i j)) (hv i j) H ≪≫ e (m i j) =
    (GroupScheme.baseChange (v i)).mapIso (e j) ≪≫ e i)

/-- Actual integral Čech data from a finite normalized component cover and
semilinear isomorphisms whose generic fibres satisfy the tower law. -/
def datumOfGenericSemilinear : Datum p N.group :=
  SemilinearComponents.datumOfSemilinear p q a hf hg m hm N.group n
    (fun i j => semilinear_tower_of_generic N (a i) (a j) (a (m i j)) (hm i j)
      (v i) (v j) (v (m i j)) (hv i j) (hvc i) (hvc j) (hvc (m i j))
      (n i) (n j) (n (m i j)) (e i) (e j) (e (m i j)) (hn i) (hn j)
      (hn (m i j)) (he i j))

/-- The constructed datum has the original normalized integral components. -/
theorem pullIso_datumOfGenericSemilinear (i : I) :
    pullIso (q i) (hf i) (hg i)
        (datumOfGenericSemilinear N p q a v hf hg m hm hv hvc n e hn he).overlap =
      semilinearComponent N.group (n i) :=
  SemilinearComponents.pullIso_datumOfSemilinear p q a hf hg m hm N.group n _ i

end Components

section Galois

open GaloisPointComparison

variable (k : Type u) [Field k] [Algebra k L]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- The named canonical Galois comparison satisfies the tower law with the
actual scheme-map composition supplied explicitly. -/
theorem galoisDescentIso_tower (σ τ υ : L ≃ₐ[k] L)
    (hστ : galoisBaseMap k L σ ≫ galoisBaseMap k L τ = galoisBaseMap k L υ) :
    pullbackComparison (galoisBaseMap k L τ) (galoisBaseMap k L σ)
        (galoisBaseMap k L υ) hστ (baseChanged k L G) ≪≫ galoisDescentIso k L G υ =
      (GroupScheme.baseChange (galoisBaseMap k L σ)).mapIso
        (galoisDescentIso k L G τ) ≪≫ galoisDescentIso k L G σ := by
  simp only [galoisDescentIso_def]
  exact descentBaseChangeIso_tower (baseMap k L) (galoisBaseMap k L σ)
    (galoisBaseMap k L τ) (galoisBaseMap k L υ) hστ
    (galoisBaseMap_over k L σ) (galoisBaseMap_over k L τ)
    (galoisBaseMap_over k L υ) G

variable (P : IntegralModel R L (baseChanged k L G))
  {B : Scheme.{u}} (p : Spec (CommRingCat.of R) ⟶ B) {I : Type}
  (q : I → (Spec (CommRingCat.of R) ⟶ Overlap p))
  [∀ i, IsIso (q i ≫ fst p)] [Finite I] [IsIso (Sigma.desc q)]
  (a : I → (Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))) [∀ i, IsIso (a i)]
  (σ : I → (L ≃ₐ[k] L))
  (hf : ∀ i, q i ≫ fst p = 𝟙 _) (hg : ∀ i, q i ≫ snd p = a i)
  (m : I → I → I) (hm : ∀ i j, a i ≫ a j = a (m i j))
  (hv : ∀ i j, galoisBaseMap k L (σ i) ≫ galoisBaseMap k L (σ j) =
    galoisBaseMap k L (σ (m i j)))
  (hvc : ∀ i, galoisBaseMap k L (σ i) ≫ Spec.algebraMap R L =
    Spec.algebraMap R L ≫ a i)
  (hext : HasSmoothHomExtension (R := R) (L := L)) (hP : P.IsSmooth)
  (hstable : ∀ i, ∀ g ∈ P.integralPoints,
    rationalConjugate k L G (σ i) g ∈ P.integralPoints)
  (hstable' : ∀ i, ∀ g ∈ P.integralPoints,
    rationalConjugate k L G (σ i).symm g ∈ P.integralPoints)

/-- Stable points and a supplied extension property give actual coherent
integral descent data on any supplied finite normalized component cover. -/
def datumOfStableGaloisPoints : Datum p P.group :=
  datumOfGenericSemilinear P p q a (fun i => galoisBaseMap k L (σ i)) hf hg m hm hv hvc
    (fun i => (galoisTwistIso k G P (σ i) (a i) (hvc i) hext hP
      (hstable i) (hstable' i)).iso)
    (fun i => galoisDescentIso k L G (σ i))
    (fun i => Hom.twist_generic_comm P (a i) (galoisBaseMap k L (σ i)) (hvc i)
      (galoisTwistIso k G P (σ i) (a i) (hvc i) hext hP
        (hstable i) (hstable' i)).toHom)
    (fun i j => galoisDescentIso_tower k G (σ i) (σ j) (σ (m i j)) (hv i j))

/-- Its normalized components recover exactly the constructed integral
Galois semilinear isomorphisms. -/
theorem pullIso_datumOfStableGaloisPoints (i : I) :
    pullIso (q i) (hf i) (hg i)
        (datumOfStableGaloisPoints k G P p q a σ hf hg m hm hv hvc hext hP
          hstable hstable').overlap =
      semilinearComponent P.group
        (galoisTwistIso k G P (σ i) (a i) (hvc i) hext hP
          (hstable i) (hstable' i)).iso :=
  pullIso_datumOfGenericSemilinear P p q a (fun j => galoisBaseMap k L (σ j))
    hf hg m hm hv hvc _ _ _ _ i

end Galois

end Langlands.GroupScheme.IntegralModel
