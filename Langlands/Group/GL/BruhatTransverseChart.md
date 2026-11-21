# Straightening the transverse matrix field

For a nonzero normal matrix \(X\), take a real continuous linear functional \(h\) with \(h(X)=1\). Its kernel and the real line spanned by \(X\) split the normal direction space. With \(Y\) in that kernel, the chart map is

\[
(U,R,Y,t)\longmapsto \exp(tX)(1+Y)b(1+U)(1+R)p.
\]

The two normal factors have derivative \(Y+tX\) at zero. Together with the tangent factors they give the invertible derivative computed in `BruhatMatrixChartDifferential`. The real inverse function theorem gives an open chart with smooth inverse near \(bp\). Throughout the parameter space, differentiation in \(t\) has value \(X\) times the chart map, by the matrix exponential derivative.

This is a derived matrix construction for the transverse coordinate used in Shalika's Proposition 2.10, printed p. 182.
